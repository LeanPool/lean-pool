/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk015Compact001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part043`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_isocutstrictsegresndv`. -/
@[expose]
noncomputable def gIsocutstrictsegresndv (x : Var) (y : Var) (z : Var) (v : Var)
    (D : Class) (R : Class) (S : Class) (E : Class) (H : Class)
    (hyp_isocutstrictsegresndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_isocutstrictsegresndv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
              (.classMem (.cv x) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synWiso H
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classEq (.cv z) (synCfv H (.cv x)))) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))) :=
  by
  have p0000 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classEq (.cv z) (synCfv H (.cv x)))
  have p0001 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0000 p0001
  have p0004 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0005 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0000 p0004
  have p0006 :=
    @gSimpr (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0005 p0006
  have p0008 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0002 p0007
  have p0009 :=
    @gIsostrictsegresndv x
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) H
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (synCres H (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))) (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCxp (synCin
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))))
        (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      p0008 p0009
  have p0011 :=
    @gA1i (synWbr R (synCwe) D)
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      hyp_isocutstrictsegresndv_1
  have p0015 :=
    @gSimpl (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0016 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) p0005 p0015
  have p0017 := @gSimpl (.classMem (.cv y) D) (.classMem (.cv v) E)
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv y) D) p0016
      p0017
  have p0019 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWbr R (synCwe) D) (.classMem (.cv y) D) p0011 p0018
  have p0025 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0019 p0007
  have p0026 := @gStrictsegcut x y D R
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0025 p0026
  have p0028 :=
    @gReseq2d
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) H p0027
  have p0029 :=
    @gIsoeq1
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      (synCin (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCxp (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x))))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCres H (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
  have p0030 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.classEq (synCres H (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))) (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWb (synWiso (synCres H (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))) (synCin
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCxp (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
              (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid)))
                  (synCsn (synCfv H (.cv x))))))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCxp (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
              (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid)))
                  (synCsn (synCfv H (.cv x))))))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0028 p0029
  have p0031 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWiso (synCres H (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))) (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCxp (synCin
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))))
        (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCxp (synCin
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))))
        (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      p0010 p0030
  have p0066 :=
    @gXpeq12d
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0027
      p0027
  have p0067 :=
    @gIneq2d
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCxp (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0066
  have p0085 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0027
  have p0086 :=
    @gInss1 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCima (synCcnv (synCdif (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCid))) (synCsn (.cv x)))
  have p0087 :=
    @gA1i
      (synWss (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      p0086
  have p0088 :=
    @gEqsstrd
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) p0085
      p0087
  have p0089 := @gStrictsegrestrnest x y D R
  have p0090 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classEq (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0088 p0089
  have p0091 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0067 p0090
  have p0092 :=
    @gIsoeq2
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      (synCin (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCxp (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x))))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0093 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.classEq (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCxp (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
              (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid)))
                  (synCsn (synCfv H (.cv x))))))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCxp (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
              (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid)))
                  (synCsn (synCfv H (.cv x))))))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0091 p0092
  have p0094 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCxp (synCin
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))))
        (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCxp (synCin
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))))
        (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      p0031 p0093
  have p0095 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classEq (.cv z) (synCfv H (.cv x)))
  have p0096 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.cv z) (synCfv H (.cv x)) p0095
  have p0097 := @gSneq (synCfv H (.cv x)) (.cv z)
  have p0098 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.classEq (synCfv H (.cv x)) (.cv z))
      (.classEq (synCsn (synCfv H (.cv x))) (synCsn (.cv z))) p0096 p0097
  have p0099 :=
    @gImaeq2d
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCsn (synCfv H (.cv x))) (synCsn (.cv z))
      (synCcnv (synCdif (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCid)))
      p0098
  have p0100 :=
    @gIneq2d
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCima (synCcnv (synCdif (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCid))) (synCsn (synCfv H (.cv x))))
      (synCima (synCcnv (synCdif (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCid))) (synCsn (.cv z)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) p0099
  have p0101 :=
    @gA1i (synWbr S (synCwe) E)
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      hyp_isocutstrictsegresndv_2
  have p0107 := @gSimpr (.classMem (.cv y) D) (.classMem (.cv v) E)
  have p0108 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv v) E) p0016
      p0107
  have p0109 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWbr S (synCwe) E) (.classMem (.cv v) E) p0101 p0108
  have p0113 :=
    @gIsof1o (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      H
  have p0114 :=
    @gF1of (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) H
  have p0115 :=
    @gSyl
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWf1o H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWf H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0113 p0114
  have p0116 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWf H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0002 p0115
  have p0122 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWf H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0116 p0007
  have p0123 :=
    @gFfvelrn (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (.cv x) H
  have p0124 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWf H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCfv H (.cv x))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0122 p0123
  have p0127 :=
    @gEleq1 (synCfv H (.cv x)) (.cv z)
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
  have p0128 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.classEq (synCfv H (.cv x)) (.cv z))
      (synWb (.classMem (synCfv H (.cv x))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (.classMem (.cv z)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0096 p0127
  have p0129 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.classMem (synCfv H (.cv x))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (.classMem (.cv z)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0124 p0128
  have p0130 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWbr S (synCwe) E) (.classMem (.cv v) E))
      (.classMem (.cv z)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0109 p0129
  have p0131 := @gStrictsegcut z v E S
  have p0132 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWa (synWa (synWbr S (synCwe) E) (.classMem (.cv v) E)) (.classMem (.cv z)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classEq (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))
      p0130 p0131
  have p0133 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (.cv z))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))) p0100
      p0132
  have p0173 :=
    @gXpeq12d
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))) p0133
      p0133
  have p0174 :=
    @gIneq2d
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCxp (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0173
  have p0214 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))) p0133
  have p0215 :=
    @gInss1 (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      (synCima (synCcnv (synCdif (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCid))) (synCsn (synCfv H (.cv x))))
  have p0216 :=
    @gA1i
      (synWss (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x)))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      p0215
  have p0217 :=
    @gEqsstrd
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) p0214
      p0216
  have p0218 := @gStrictsegrestrnest z v E S
  have p0219 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWss (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (.classEq (synCin (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))))
      p0217 p0218
  have p0220 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synCin (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCxp (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x))))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))))
      (synCin (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
      p0174 p0219
  have p0221 :=
    @gIsoeq3
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCxp (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x))))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0222 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.classEq (synCin (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCxp (synCin
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCxp (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
              (synCin
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv v)))))) (synCid)))
                  (synCsn (synCfv H (.cv x))))))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
          (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0220 p0221
  have p0223 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCxp (synCin
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv v)))))) (synCid))) (synCsn (synCfv H (.cv x)))))))
        (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
        (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      p0094 p0222
  have p0241 :=
    @gIsoeq4
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0242 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.classEq (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
          (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0027 p0241
  have p0243 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
        (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      p0223 p0242
  have p0283 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCima (synCcnv (synCdif (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0284 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (.classEq (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x)))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
              (synCcnv (synCdif (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCid))) (synCsn (synCfv H (.cv x)))))) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
      p0133 p0283
  have p0285 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classEq (.cv z) (synCfv H (.cv x))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCima
            (synCcnv (synCdif (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))
      p0243 p0284
  exact p0285


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part044`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisocompatndv`. -/
@[expose]
noncomputable def gWecutisocompatndv (x : Var) (y : Var) (v : Var) (u : Var) (D : Class)
    (R : Class) (S : Class) (f : Var) (g : Var) (E : Class)
    (hyp_wecutisocompatndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisocompatndv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (synWa (.classMem (.cv u) E) (.classMem (.cv v) E))) (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWa (synWiso (.cv f) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
            (synWiso (.cv g) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (.classEq (.cv f) (synCres (.cv g) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ v } : Finset Var) ∪
                  ({ u } : Finset Var) ∪
                D.fv ∪
              R.fv ∪
            S.fv ∪
          ({ f } : Finset Var) ∪
        ({ g } : Finset Var) ∪
      E.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_g : z ≠ g := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_not_E : z ∉ E.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((synCfv (.cv g) (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_g, or_false, not_false_eq_true])
  have dv_cache_0002 :
    z ∉
      ((synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (synWa (.classMem (.cv u) E) (.classMem (.cv v) E))) (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synWa (synWiso (.cv f) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
            (synWiso (.cv g) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_D, fresh_z_ne_y, fresh_z_ne_u,
          fresh_z_not_E, fresh_z_ne_v, fresh_z_not_R, fresh_z_not_S, fresh_z_ne_f,
          fresh_z_ne_g, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((Wff.classEq (.cv f) (synCres (.cv g) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_f, fresh_z_ne_g, fresh_z_not_D, fresh_z_not_R,
          fresh_z_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  let syntaxFormula0000 : Wff :=
    (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (.classMem (.cv u) E) (.classMem (.cv v) E)))
  let syntaxFormula0001 : Wff :=
    (.classMem (.cv x)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  let syntaxFormula0002 : Wff := (synWa syntaxFormula0000 syntaxFormula0001)
  let syntaxClass0003 : Class :=
    (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxClass0004 : Class := (synCin R syntaxClass0003)
  let syntaxClass0005 : Class :=
    (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  let syntaxClass0006 : Class := (synCin S syntaxClass0005)
  let syntaxFormula0007 : Wff :=
    (synWiso (.cv f) syntaxClass0004 syntaxClass0006
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  let syntaxClass0008 : Class :=
    (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  let syntaxClass0009 : Class := (synCin R syntaxClass0008)
  let syntaxClass0010 : Class :=
    (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  let syntaxClass0011 : Class := (synCin S syntaxClass0010)
  let syntaxFormula0012 : Wff :=
    (synWiso (.cv g) syntaxClass0009 syntaxClass0011
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  let syntaxFormula0013 : Wff := (synWa syntaxFormula0007 syntaxFormula0012)
  let syntaxFormula0014 : Wff := (synWa syntaxFormula0002 syntaxFormula0013)
  let syntaxFormula0015 : Wff :=
    (synWa (.classEq (.cv z) (synCfv (.cv g) (.cv x))) syntaxFormula0014)
  let syntaxFormula0016 : Wff := (synWex z syntaxFormula0015)
  let syntaxClass0017 : Class :=
    (synCres (.cv g)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0018 : Wff := (.classMem syntaxClass0017 (synCvv))
  let syntaxFormula0019 : Wff :=
    (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) syntaxFormula0001)
  let syntaxFormula0020 : Wff := (synWa syntaxFormula0019 syntaxFormula0012)
  let syntaxFormula0021 : Wff :=
    (synWa syntaxFormula0020 (.classEq (.cv z) (synCfv (.cv g) (.cv x))))
  let syntaxClass0022 : Class :=
    (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))
  let syntaxClass0023 : Class := (synCin S syntaxClass0022)
  let syntaxFormula0024 : Wff :=
    (synWiso syntaxClass0017 syntaxClass0004 syntaxClass0023
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))
  let syntaxFormula0025 : Wff :=
    (synWf1o (.cv g) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  let syntaxFormula0026 : Wff :=
    (synWf (.cv g) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  let syntaxFormula0027 : Wff := (synWa syntaxFormula0026 syntaxFormula0001)
  let syntaxFormula0028 : Wff :=
    (.classMem (synCfv (.cv g) (.cv x))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  let syntaxFormula0029 : Wff :=
    (.classMem (.cv z)
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  let syntaxFormula0030 : Wff := (synWb syntaxFormula0029 syntaxFormula0028)
  let syntaxClass0031 : Class := (synCcom syntaxClass0017 (synCcnv (.cv f)))
  let syntaxFormula0032 : Wff := (.classMem syntaxClass0031 (synCvv))
  let syntaxFormula0033 : Wff :=
    (synWiso (synCcnv (.cv f)) syntaxClass0006 syntaxClass0004
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0034 : Wff := (synWa syntaxFormula0033 syntaxFormula0024)
  let syntaxFormula0035 : Wff :=
    (synWiso syntaxClass0031 syntaxClass0006 syntaxClass0023
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))
  let syntaxFormula0036 : Wff :=
    (synWa (synWa (.classMem (.cv u) E) (.classMem (.cv z) E)) syntaxFormula0032)
  let syntaxFormula0037 : Wff := (synWa syntaxFormula0036 syntaxFormula0035)
  let syntaxFormula0038 : Wff :=
    (synWiso syntaxClass0017 syntaxClass0004 syntaxClass0006
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))))
  let syntaxFormula0039 : Wff :=
    (synWiso syntaxClass0017 syntaxClass0004 syntaxClass0006
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  let syntaxFormula0040 : Wff := (synWa syntaxFormula0007 syntaxFormula0039)
  let syntaxFormula0041 : Wff := (.classEq (.cv f) syntaxClass0017)
  have p0000 := @gFvex (.cv x) (.cv g)
  have p0001 := @gBiid syntaxFormula0014
  have p0002 :=
    @gA1i (synWb syntaxFormula0014 syntaxFormula0014)
      (.classEq (.cv z) (synCfv (.cv g) (.cv x))) p0001
  have p0003 :=
    @gCeqsexv syntaxFormula0014 syntaxFormula0014 z (synCfv (.cv g) (.cv x))
      dv_cache_0001 dv_cache_0002 p0000 p0002
  have p0004 := @gBiimpri syntaxFormula0016 syntaxFormula0014 p0003
  have p0005 := @gVex f
  have p0006 := @gA1i (.classMem (.cv f) (synCvv)) syntaxFormula0015 p0005
  have p0007 := @gVex g
  have p0008 := @gBrex R D (synCwe)
  have p0009 := Nominal.mp hyp_wecutisocompatndv_1 p0008
  have p0010 := @gSimpr (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0011 := Nominal.mp p0009 p0010
  have p0014 := @gSimpl (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0015 := Nominal.mp p0009 p0014
  have p0016 := @gIdex
  have p0017 := @gDifex R (synCid) p0015 p0016
  have p0018 := @gCnvex (synCdif R (synCid)) p0017
  have p0019 := @gSnex (.cv x)
  have p0020 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) p0018 p0019
  have p0021 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0011 p0020
  have p0022 :=
    @gResex (.cv g)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0007
      p0021
  have p0023 := @gA1i syntaxFormula0018 syntaxFormula0015 p0022
  have p0024 :=
    @gJca syntaxFormula0015 (.classMem (.cv f) (synCvv)) syntaxFormula0018 p0006 p0023
  have p0025 := @gSimpr (.classEq (.cv z) (synCfv (.cv g) (.cv x))) syntaxFormula0014
  have p0026 := @gSimpr syntaxFormula0002 syntaxFormula0013
  have p0027 := @gSimpl syntaxFormula0007 syntaxFormula0012
  have p0028 := @gSyl syntaxFormula0014 syntaxFormula0013 syntaxFormula0007 p0026 p0027
  have p0029 := @gSyl syntaxFormula0015 syntaxFormula0014 syntaxFormula0007 p0025 p0028
  have p0031 := @gSimpl syntaxFormula0002 syntaxFormula0013
  have p0032 := @gSimpl syntaxFormula0000 syntaxFormula0001
  have p0033 := @gSyl syntaxFormula0014 syntaxFormula0002 syntaxFormula0000 p0031 p0032
  have p0034 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (.classMem (.cv u) E) (.classMem (.cv v) E))
  have p0035 :=
    @gSyl syntaxFormula0014 syntaxFormula0000
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) p0033 p0034
  have p0036 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0037 :=
    @gSyl syntaxFormula0014 (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classMem (.cv y) D) p0035 p0036
  have p0038 :=
    @gSyl syntaxFormula0015 syntaxFormula0014 (.classMem (.cv y) D) p0025 p0037
  have p0043 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (.classMem (.cv u) E) (.classMem (.cv v) E))
  have p0044 :=
    @gSyl syntaxFormula0014 syntaxFormula0000
      (synWa (.classMem (.cv u) E) (.classMem (.cv v) E)) p0033 p0043
  have p0045 := @gSimpr (.classMem (.cv u) E) (.classMem (.cv v) E)
  have p0046 :=
    @gSyl syntaxFormula0014 (synWa (.classMem (.cv u) E) (.classMem (.cv v) E))
      (.classMem (.cv v) E) p0044 p0045
  have p0047 :=
    @gSyl syntaxFormula0015 syntaxFormula0014 (.classMem (.cv v) E) p0025 p0046
  have p0048 :=
    @gJca syntaxFormula0015 (.classMem (.cv y) D) (.classMem (.cv v) E) p0038 p0047
  have p0051 := @gSimpr syntaxFormula0000 syntaxFormula0001
  have p0052 := @gSyl syntaxFormula0014 syntaxFormula0002 syntaxFormula0001 p0031 p0051
  have p0053 := @gSyl syntaxFormula0015 syntaxFormula0014 syntaxFormula0001 p0025 p0052
  have p0054 :=
    @gJca syntaxFormula0015 (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
      syntaxFormula0001 p0048 p0053
  have p0057 := @gSimpr syntaxFormula0007 syntaxFormula0012
  have p0058 := @gSyl syntaxFormula0014 syntaxFormula0013 syntaxFormula0012 p0026 p0057
  have p0059 := @gSyl syntaxFormula0015 syntaxFormula0014 syntaxFormula0012 p0025 p0058
  have p0060 := @gJca syntaxFormula0015 syntaxFormula0019 syntaxFormula0012 p0054 p0059
  have p0061 := @gSimpl (.classEq (.cv z) (synCfv (.cv g) (.cv x))) syntaxFormula0014
  have p0062 :=
    @gJca syntaxFormula0015 syntaxFormula0020
      (.classEq (.cv z) (synCfv (.cv g) (.cv x))) p0060 p0061
  have p0063 :=
    @gIsocutstrictsegresndv x y z v D R S E (.cv g) hyp_wecutisocompatndv_1
      hyp_wecutisocompatndv_2
  have p0064 := @gSyl syntaxFormula0015 syntaxFormula0021 syntaxFormula0024 p0062 p0063
  have p0071 := @gSimpl (.classMem (.cv u) E) (.classMem (.cv v) E)
  have p0072 :=
    @gSyl syntaxFormula0014 (synWa (.classMem (.cv u) E) (.classMem (.cv v) E))
      (.classMem (.cv u) E) p0044 p0071
  have p0073 :=
    @gSyl syntaxFormula0015 syntaxFormula0014 (.classMem (.cv u) E) p0025 p0072
  have p0079 :=
    @gIsof1o (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      syntaxClass0009 syntaxClass0011 (.cv g)
  have p0080 :=
    @gF1of (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (.cv g)
  have p0081 := @gSyl syntaxFormula0012 syntaxFormula0025 syntaxFormula0026 p0079 p0080
  have p0082 := @gSyl syntaxFormula0015 syntaxFormula0012 syntaxFormula0026 p0059 p0081
  have p0088 := @gJca syntaxFormula0015 syntaxFormula0026 syntaxFormula0001 p0082 p0053
  have p0089 :=
    @gFfvelrn (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (.cv x)
      (.cv g)
  have p0090 := @gSyl syntaxFormula0015 syntaxFormula0027 syntaxFormula0028 p0088 p0089
  have p0092 :=
    @gEleq1 (.cv z) (synCfv (.cv g) (.cv x))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
  have p0093 :=
    @gSyl syntaxFormula0015 (.classEq (.cv z) (synCfv (.cv g) (.cv x)))
      syntaxFormula0030 p0061 p0092
  have p0094 :=
    @gMpbird syntaxFormula0015 syntaxFormula0029 syntaxFormula0028 p0090 p0093
  have p0095 := @gInss1 E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))
  have p0096 :=
    @gSseli (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) E
      (.cv z) p0095
  have p0097 :=
    @gSyl syntaxFormula0015 syntaxFormula0029 (.classMem (.cv z) E) p0094 p0096
  have p0098 :=
    @gJca syntaxFormula0015 (.classMem (.cv u) E) (.classMem (.cv z) E) p0073 p0097
  have p0116 := @gCnvex (.cv f) p0005
  have p0117 := @gCoex syntaxClass0017 (synCcnv (.cv f)) p0022 p0116
  have p0118 := @gA1i syntaxFormula0032 syntaxFormula0015 p0117
  have p0119 :=
    @gJca syntaxFormula0015 (synWa (.classMem (.cv u) E) (.classMem (.cv z) E))
      syntaxFormula0032 p0098 p0118
  have p0125 :=
    @gIsocnv (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      syntaxClass0004 syntaxClass0006 (.cv f)
  have p0126 := @gSyl syntaxFormula0015 syntaxFormula0007 syntaxFormula0033 p0029 p0125
  have p0162 := @gJca syntaxFormula0015 syntaxFormula0033 syntaxFormula0024 p0126 p0064
  have p0163 :=
    @gIsotr (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
      syntaxClass0006 syntaxClass0004 syntaxClass0023 syntaxClass0017 (synCcnv (.cv f))
  have p0164 := @gSyl syntaxFormula0015 syntaxFormula0034 syntaxFormula0035 p0162 p0163
  have p0165 := @gJca syntaxFormula0015 syntaxFormula0036 syntaxFormula0035 p0119 p0164
  have p0166 := @gWecutisoendpointseqndv u z E S syntaxClass0031 hyp_wecutisocompatndv_2
  have p0167 :=
    @gSyl syntaxFormula0015 syntaxFormula0037 (.classEq (.cv u) (.cv z)) p0165 p0166
  have p0168 := @gSneq (.cv u) (.cv z)
  have p0169 :=
    @gSyl syntaxFormula0015 (.classEq (.cv u) (.cv z))
      (.classEq (synCsn (.cv u)) (synCsn (.cv z))) p0167 p0168
  have p0170 :=
    @gImaeq2d syntaxFormula0015 (synCsn (.cv u)) (synCsn (.cv z))
      (synCcnv (synCdif S (synCid))) p0169
  have p0171 :=
    @gIneq2d syntaxFormula0015
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))) E p0170
  have p0279 :=
    @gXpeq12d syntaxFormula0015
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))) p0171
      p0171
  have p0280 := @gIneq2d syntaxFormula0015 syntaxClass0005 syntaxClass0022 S p0279
  have p0281 := @gEqcomd syntaxFormula0015 syntaxClass0006 syntaxClass0023 p0280
  have p0282 :=
    @gIsoeq3 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
      syntaxClass0004 syntaxClass0023 syntaxClass0006 syntaxClass0017
  have p0283 :=
    @gSyl syntaxFormula0015 (.classEq syntaxClass0023 syntaxClass0006)
      (synWb syntaxFormula0024 syntaxFormula0038) p0281 p0282
  have p0284 := @gMpbid syntaxFormula0015 syntaxFormula0024 syntaxFormula0038 p0064 p0283
  have p0392 :=
    @gEqcomd syntaxFormula0015
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z)))) p0171
  have p0393 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      syntaxClass0004 syntaxClass0006 syntaxClass0017
  have p0394 :=
    @gSyl syntaxFormula0015
      (.classEq (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWb syntaxFormula0038 syntaxFormula0039) p0392 p0393
  have p0395 := @gMpbid syntaxFormula0015 syntaxFormula0038 syntaxFormula0039 p0284 p0394
  have p0396 := @gJca syntaxFormula0015 syntaxFormula0007 syntaxFormula0039 p0029 p0395
  have p0397 :=
    @gJca syntaxFormula0015 (synWa (.classMem (.cv f) (synCvv)) syntaxFormula0018)
      syntaxFormula0040 p0024 p0396
  have p0398 :=
    @gWecutisouniquecl (.cv x) (.cv u) D R S E (.cv f) syntaxClass0017
      hyp_wecutisocompatndv_1 hyp_wecutisocompatndv_2
  have p0399 :=
    @gSyl syntaxFormula0015
      (synWa (synWa (.classMem (.cv f) (synCvv)) syntaxFormula0018) syntaxFormula0040)
      syntaxFormula0041 p0397 p0398
  have p0400 := @gExlimiv syntaxFormula0015 syntaxFormula0041 z dv_cache_0003 p0399
  have p0401 := @gSyl syntaxFormula0014 syntaxFormula0016 syntaxFormula0041 p0004 p0400
  exact p0401


end NFChoice.DirectNominalPrf.WPPReplay

end
