/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk016Compact001Part001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisochainndv (x : Var) (y : Var) (v : Var) (u : Var) (D : Class)
    (R : Class) (S : Class) (f : Var) (g : Var) (E : Class)
    (hyp_wecutisochainndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisochainndv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) :=
  by
  have p0000 := @g_wppweconnex D R
  have p0001 := Nominal.mp hyp_wecutisochainndv_1 p0000
  have p0002 :=
    @g_a1i (syn_wbr R (syn_cconnex) D)
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      p0001
  have p0003 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wne (.cv x) (.cv y))
  have p0004 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
  have p0005 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) p0004 p0005
  have p0007 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0006
      p0007
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classMem (.cv x) D) p0003 p0008
  have p0014 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0006
      p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classMem (.cv y) D) p0003 p0015
  have p0017 :=
    @g_connexd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      D R (.cv x) (.cv y) p0002 p0009 p0016
  have p0018 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      p0003 p0004
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      p0018 p0021
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0018 p0009
  have p0032 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0034 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wne (.cv x) (.cv y))
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wne (.cv x) (.cv y)) p0018 p0034
  have p0036 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)) p0032 p0035
  have p0037 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))
      p0031 p0036
  have p0038 := @g_elstrictseg y x D R
  have p0039 :=
    @g_biimpri
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0037 p0039
  have p0041 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0022 p0040
  have p0044 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0003 p0044
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0018 p0045
  have p0047 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0041 p0046
  have p0048 :=
    @g_wecutisocompatndv x y v u D R S f g E hyp_wecutisochainndv_1 hyp_wecutisochainndv_2
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa
          (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classEq (.cv f) (syn_cres (.cv g)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0047 p0048
  have p0050 :=
    @g_resss (.cv g)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0051 :=
    @g_a1i
      (syn_wss (syn_cres (.cv g)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv g))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      p0050
  have p0052 :=
    @g_eqsstrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.cv f)
      (syn_cres (.cv g)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.cv g) p0049 p0051
  have p0053 := @g_orc (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wss (.cv f) (.cv g))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0052 p0053
  have p0055 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0054
  have p0056 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0056 p0016
  have p0073 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0056 p0009
  have p0074 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (.classMem (.cv x) D) p0064 p0073
  have p0078 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))
  have p0079 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)) p0004 p0078
  have p0080 := @g_simpr (.classMem (.cv u) E) (.classMem (.cv v) E)
  have p0081 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)) (.classMem (.cv v) E) p0079
      p0080
  have p0082 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classMem (.cv v) E) p0003 p0081
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv v) E) p0056 p0082
  have p0089 := @g_simpl (.classMem (.cv u) E) (.classMem (.cv v) E)
  have p0090 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)) (.classMem (.cv u) E) p0079
      p0089
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classMem (.cv u) E) p0003 p0090
  have p0092 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv u) E) p0056 p0091
  have p0093 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (.classMem (.cv v) E) (.classMem (.cv u) E) p0083 p0092
  have p0094 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) D))
      (syn_wa (.classMem (.cv v) E) (.classMem (.cv u) E)) p0074 p0093
  have p0104 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
  have p0107 :=
    @g_necomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0034
  have p0108 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wne (.cv y) (.cv x)) p0056 p0107
  have p0109 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0104 p0108
  have p0110 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
      p0064 p0109
  have p0111 := @g_elstrictseg x y D R
  have p0112 :=
    @g_biimpri
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0111
  have p0113 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0110 p0112
  have p0114 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) D))
        (syn_wa (.classMem (.cv v) E) (.classMem (.cv u) E)))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0094 p0113
  have p0118 :=
    @g_simpr
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  have p0119 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0044 p0118
  have p0120 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0003 p0119
  have p0121 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0056 p0120
  have p0125 :=
    @g_simpl
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  have p0126 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0044 p0125
  have p0127 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0003 p0126
  have p0128 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0056 p0127
  have p0129 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0121 p0128
  have p0130 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) D))
          (syn_wa (.classMem (.cv v) E) (.classMem (.cv u) E))) (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0114 p0129
  have p0131 :=
    @g_wecutisocompatndv y x u v D R S g f E hyp_wecutisochainndv_1 hyp_wecutisochainndv_2
  have p0132 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) D))
            (syn_wa (.classMem (.cv v) E) (.classMem (.cv u) E))) (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
          (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (.classEq (.cv g) (syn_cres (.cv f)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0130 p0131
  have p0133 :=
    @g_resss (.cv f)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
  have p0134 :=
    @g_a1i
      (syn_wss (syn_cres (.cv f)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.cv f))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      p0133
  have p0135 :=
    @g_eqsstrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (.cv g)
      (syn_cres (.cv f)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.cv f) p0132 p0134
  have p0136 := @g_olc (syn_wss (.cv g) (.cv f)) (syn_wss (.cv f) (.cv g))
  have p0137 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
              (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wss (.cv g) (.cv f))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0135 p0136
  have p0138 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0137
  have p0139 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))
      (syn_wbr (.cv y) R (.cv x)) p0055 p0138
  have p0140 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_wne (.cv x) (.cv y)))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0017 p0139
  have p0141 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wne (.cv x) (.cv y))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0140
  have p0142 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.neg (syn_wne (.cv x) (.cv y)))
  have p0148 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classMem (.cv x) D) p0142 p0008
  have p0155 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classMem (.cv u) E) p0142 p0090
  have p0162 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classMem (.cv v) E) p0142 p0081
  have p0163 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (.classMem (.cv u) E) (.classMem (.cv v) E) p0155 p0162
  have p0164 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (.classMem (.cv x) D) (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)) p0148
      p0163
  have p0169 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0142 p0126
  have p0174 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0142 p0119
  have p0175 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.neg (syn_wne (.cv x) (.cv y)))
  have p0176 := @g_nne (.cv x) (.cv y)
  have p0177 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (.neg (syn_wne (.cv x) (.cv y))) (.classEq (.cv x) (.cv y)) p0175 p0176
  have p0178 := @g_sneq (.cv x) (.cv y)
  have p0179 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (.classEq (.cv x) (.cv y)) (.classEq (syn_csn (.cv x)) (syn_csn (.cv y))) p0177
      p0178
  have p0180 :=
    @g_imaeq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_ccnv (syn_cdif R (syn_cid))) p0179
  have p0181 :=
    @g_ineq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) D p0180
  have p0189 :=
    @g_xpeq12d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0181
      p0181
  have p0190 :=
    @g_ineq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      R p0189
  have p0191 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0190
  have p0192 :=
    @g_isoeq2 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.cv g)
  have p0193 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (.classEq (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wb (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0191 p0192
  have p0194 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0174 p0193
  have p0202 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0181
  have p0203 :=
    @g_isoeq4 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.cv g)
  have p0204 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wb (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0202 p0203
  have p0205 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0194 p0204
  have p0206 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wiso (.cv g) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0169 p0205
  have p0207 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wa (.classMem (.cv x) D) (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wiso (.cv g) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0164 p0206
  have p0208 :=
    @g_wecutisosamesourcendv x v u D R S f g E hyp_wecutisochainndv_1
      hyp_wecutisochainndv_2
  have p0209 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wa (syn_wa (.classMem (.cv x) D)
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (.classEq (.cv u) (.cv v)) (.classEq (.cv f) (.cv g))) p0207 p0208
  have p0210 := @g_simpr (.classEq (.cv u) (.cv v)) (.classEq (.cv f) (.cv g))
  have p0211 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wa (.classEq (.cv u) (.cv v)) (.classEq (.cv f) (.cv g)))
      (.classEq (.cv f) (.cv g)) p0209 p0210
  have p0212 := @g_eqimss (.cv f) (.cv g)
  have p0213 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (.classEq (.cv f) (.cv g)) (syn_wss (.cv f) (.cv g)) p0211 p0212
  have p0215 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
            (syn_wiso (.cv g) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (.neg (syn_wne (.cv x) (.cv y))))
      (syn_wss (.cv f) (.cv g))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0213 p0053
  have p0216 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.neg (syn_wne (.cv x) (.cv y)))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0215
  have p0217 :=
    @g_pm2_61d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (syn_wa (syn_wiso (.cv f)
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
          (syn_wiso (.cv g) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wne (.cv x) (.cv y))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0141 p0216
  exact p0217


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_elwecutiso (x : Var) (u : Var) (D : Class) (R : Class) (S : Class)
    (h : Var) (E : Class) (dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_u : u ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (dv_h_u : h ≠ u) (dv_h_x : h ≠ x) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv h) (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E
            (syn_wiso (.cv h) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪
        ({ h } : Finset Var) ∪
      E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_ne_x : f ≠ x := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_f : x ≠ f := Ne.symm fresh_f_ne_x
  have fresh_f_ne_u : f ≠ u := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_f : u ≠ f := Ne.symm fresh_f_ne_u
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_ne_h : f ≠ h := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_D, not_false_eq_true])
  have dv_cache_0002 : u ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_u, not_false_eq_true])
  have dv_cache_0003 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0004 : f ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_E, not_false_eq_true])
  have dv_cache_0005 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_u, not_false_eq_true])
  have dv_cache_0006 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0007 : f ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_R, not_false_eq_true])
  have dv_cache_0008 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_u, not_false_eq_true])
  have dv_cache_0009 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0010 : f ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_S, not_false_eq_true])
  have dv_cache_0011 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_u, not_false_eq_true])
  have dv_cache_0012 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0013 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0014 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0015 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0016 : u ∉ ((Wff.classEq (.cv f) (.cv h))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_f, (Ne.symm dv_h_u), or_false,
          not_false_eq_true])
  have dv_cache_0017 : x ∉ ((Wff.classEq (.cv f) (.cv h))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_f, (Ne.symm dv_h_x), or_false,
          not_false_eq_true])
  have dv_cache_0018 : f ∉ ((Class.cv h)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_h, not_false_eq_true])
  have dv_cache_0019 :
    f ∉
      ((syn_wrex x D (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E,
          fresh_f_not_R, fresh_f_ne_x, fresh_f_not_S, fresh_f_ne_u, fresh_f_ne_h,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wecutiso x u D R S f
      E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @g_eleq2i (syn_cwecutiso R D S E)
      (.cab f (syn_wrex x D (syn_wrex u E (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))))
      (.cv h) p0000
  have p0002 := @g_vex h
  have p0003 :=
    @g_isoeq1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.cv h) (.cv f)
  have p0004 :=
    @g_rexbidv (.classEq (.cv f) (.cv h))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wiso (.cv h) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      u E dv_cache_0016 p0003
  have p0005 :=
    @g_rexbidv (.classEq (.cv f) (.cv h))
      (syn_wrex u E (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      x D dv_cache_0017 p0004
  have p0006 :=
    @g_elab
      (syn_wrex x D (syn_wrex u E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (syn_wrex x D (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      f (.cv h) dv_cache_0018 dv_cache_0019 p0002 p0005
  have p0007 :=
    @g_bitri (.classMem (.cv h) (syn_cwecutiso R D S E))
      (.classMem (.cv h) (.cab f (syn_wrex x D (syn_wrex u E (syn_wiso (.cv f) (syn_cin R
                  (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))))
      (syn_wrex x D (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      p0001 p0006
  exact p0007

@[expose]
noncomputable def g_elwecutisofun11 (D : Class) (R : Class) (S : Class) (f : Var)
    (E : Class) :
    Nominal.NPrf
      (.imp (.classMem (.cv f) (syn_cwecutiso R D S E))
        (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ ({ f } : Finset Var) ∪ E.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0007 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0009 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0012 :
    x ∉ ((syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_f, or_false, not_false_eq_true])
  have dv_cache_0013 :
    u ∉ ((syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_f, or_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have p0000 :=
    @g_elwecutiso x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0001 :=
    @g_biimpi (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wrex x D (syn_wrex u E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      p0000
  have p0002 :=
    @g_isof1o (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.cv f)
  have p0003 :=
    @g_f1of (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (.cv f)
  have p0004 :=
    @g_syl
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf1o (.cv f)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf (.cv f) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0002 p0003
  have p0005 :=
    @g_ffun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (.cv f)
  have p0006 :=
    @g_syl
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf (.cv f) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wfun (.cv f)) p0004 p0005
  have p0008 :=
    @g_f1ocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (.cv f)
  have p0009 :=
    @g_syl
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf1o (.cv f)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf1o (syn_ccnv (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0002 p0008
  have p0010 :=
    @g_f1of (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_ccnv (.cv f))
  have p0011 :=
    @g_syl
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf1o (syn_ccnv (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wf (syn_ccnv (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0009 p0010
  have p0012 :=
    @g_ffun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_ccnv (.cv f))
  have p0013 :=
    @g_syl
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wf (syn_ccnv (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wfun (syn_ccnv (.cv f))) p0011 p0012
  have p0014 :=
    @g_jca
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))) p0006 p0013
  have p0015 :=
    @g_a1i
      (.imp (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
        (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) p0014
  have p0016 :=
    @g_rexlimivv
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) x u D E dv_cache_0001
      dv_cache_0012 dv_cache_0013 dv_cache_0014 p0015
  have p0017 :=
    @g_syl (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wrex x D (syn_wrex u E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) p0001 p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end
