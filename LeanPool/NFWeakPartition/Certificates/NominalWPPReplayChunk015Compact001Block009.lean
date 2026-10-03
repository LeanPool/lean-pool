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

@[expose]
noncomputable def g_isocutstrictsegresndv (x : Var) (y : Var) (z : Var) (v : Var)
    (D : Class) (R : Class) (S : Class) (E : Class) (H : Class)
    (hyp_isocutstrictsegresndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_isocutstrictsegresndv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
              (.classMem (.cv x) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso H
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (.classEq (.cv z) (syn_cfv H (.cv x)))) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.classEq (.cv z) (syn_cfv H (.cv x)))
  have p0001 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0000 p0001
  have p0004 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0000 p0004
  have p0006 :=
    @g_simpr (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0005 p0006
  have p0008 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0002 p0007
  have p0009 :=
    @g_isostrictsegresndv x
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) H
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (syn_cres H (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cxp (syn_cin
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0008 p0009
  have p0011 :=
    @g_a1i (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      hyp_isocutstrictsegresndv_1
  have p0015 :=
    @g_simpl (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) p0005 p0015
  have p0017 := @g_simpl (.classMem (.cv y) D) (.classMem (.cv v) E)
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv y) D) p0016
      p0017
  have p0019 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D) p0011 p0018
  have p0025 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0019 p0007
  have p0026 := @g_strictsegcut x y D R
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0025 p0026
  have p0028 :=
    @g_reseq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H p0027
  have p0029 :=
    @g_isoeq1
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cxp (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cres H (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.classEq (syn_cres H (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))) (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wb (syn_wiso (syn_cres H (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))) (syn_cin
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cxp (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
              (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cxp (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
              (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0028 p0029
  have p0031 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wiso (syn_cres H (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cxp (syn_cin
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cxp (syn_cin
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0010 p0030
  have p0066 :=
    @g_xpeq12d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0027
      p0027
  have p0067 :=
    @g_ineq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cxp (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0066
  have p0085 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0027
  have p0086 :=
    @g_inss1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cid))) (syn_csn (.cv x)))
  have p0087 :=
    @g_a1i
      (syn_wss (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      p0086
  have p0088 :=
    @g_eqsstrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0085
      p0087
  have p0089 := @g_strictsegrestrnest x y D R
  have p0090 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classEq (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0088 p0089
  have p0091 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0067 p0090
  have p0092 :=
    @g_isoeq2
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cxp (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0093 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.classEq (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cxp (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
              (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cxp (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
              (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0091 p0092
  have p0094 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cxp (syn_cin
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cxp (syn_cin
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0031 p0093
  have p0095 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.classEq (.cv z) (syn_cfv H (.cv x)))
  have p0096 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.cv z) (syn_cfv H (.cv x)) p0095
  have p0097 := @g_sneq (syn_cfv H (.cv x)) (.cv z)
  have p0098 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.classEq (syn_cfv H (.cv x)) (.cv z))
      (.classEq (syn_csn (syn_cfv H (.cv x))) (syn_csn (.cv z))) p0096 p0097
  have p0099 :=
    @g_imaeq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_csn (syn_cfv H (.cv x))) (syn_csn (.cv z))
      (syn_ccnv (syn_cdif (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cid)))
      p0098
  have p0100 :=
    @g_ineq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cid))) (syn_csn (syn_cfv H (.cv x))))
      (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cid))) (syn_csn (.cv z)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) p0099
  have p0101 :=
    @g_a1i (syn_wbr S (syn_cwe) E)
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      hyp_isocutstrictsegresndv_2
  have p0107 := @g_simpr (.classMem (.cv y) D) (.classMem (.cv v) E)
  have p0108 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv v) E) p0016
      p0107
  have p0109 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wbr S (syn_cwe) E) (.classMem (.cv v) E) p0101 p0108
  have p0113 :=
    @g_isof1o (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      H
  have p0114 :=
    @g_f1of (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) H
  have p0115 :=
    @g_syl
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wf1o H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wf H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0113 p0114
  have p0116 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wf H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0002 p0115
  have p0122 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wf H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0116 p0007
  have p0123 :=
    @g_ffvelrn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (.cv x) H
  have p0124 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wf H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_cfv H (.cv x))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0122 p0123
  have p0127 :=
    @g_eleq1 (syn_cfv H (.cv x)) (.cv z)
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
  have p0128 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.classEq (syn_cfv H (.cv x)) (.cv z))
      (syn_wb (.classMem (syn_cfv H (.cv x))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (.classMem (.cv z)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0096 p0127
  have p0129 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.classMem (syn_cfv H (.cv x))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (.classMem (.cv z)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0124 p0128
  have p0130 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wbr S (syn_cwe) E) (.classMem (.cv v) E))
      (.classMem (.cv z)
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      p0109 p0129
  have p0131 := @g_strictsegcut z v E S
  have p0132 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wa (syn_wa (syn_wbr S (syn_cwe) E) (.classMem (.cv v) E)) (.classMem (.cv z)
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      (.classEq (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (.cv z))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))
      p0130 p0131
  have p0133 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (.cv z))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))) p0100
      p0132
  have p0173 :=
    @g_xpeq12d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))) p0133
      p0133
  have p0174 :=
    @g_ineq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cxp (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0173
  have p0214 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))) p0133
  have p0215 :=
    @g_inss1 (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
      (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cid))) (syn_csn (syn_cfv H (.cv x))))
  have p0216 :=
    @g_a1i
      (syn_wss (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      p0215
  have p0217 :=
    @g_eqsstrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) p0214
      p0216
  have p0218 := @g_strictsegrestrnest z v E S
  have p0219 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wss (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (.classEq (syn_cin (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))))
      p0217 p0218
  have p0220 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_cin (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cxp (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      (syn_cin (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
      p0174 p0219
  have p0221 :=
    @g_isoeq3
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_cxp (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0222 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.classEq (syn_cin (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cxp (syn_cin
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cxp (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
              (syn_cin
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                              (syn_csn (.cv v)))))) (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
          (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0220 p0221
  have p0223 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_cxp (syn_cin
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv v)))))) (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
        (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0094 p0222
  have p0241 :=
    @g_isoeq4
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0242 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.classEq (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
          (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0027 p0241
  have p0243 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
        (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0223 p0242
  have p0283 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
              (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0284 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (.classEq (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                  (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
      p0133 p0283
  have p0285 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (.classEq (.cv z) (syn_cfv H (.cv x))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
                (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))
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

@[expose]
noncomputable def g_wecutisocompatndv (x : Var) (y : Var) (v : Var) (u : Var) (D : Class)
    (R : Class) (S : Class) (f : Var) (g : Var) (E : Class)
    (hyp_wecutisocompatndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisocompatndv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D
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
        (.classEq (.cv f) (syn_cres (.cv g) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) :=
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
  have dv_cache_0001 : z ∉ ((syn_cfv (.cv g) (.cv x))).fv := by
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
      ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
              (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))) (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_wa (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D
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
              (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))).fv :=
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
      ((Wff.classEq (.cv f) (syn_cres (.cv g) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv :=
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
    (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)))
  let syntaxFormula0001 : Wff :=
    (.classMem (.cv x)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  let syntaxFormula0002 : Wff := (syn_wa syntaxFormula0000 syntaxFormula0001)
  let syntaxClass0003 : Class :=
    (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxClass0004 : Class := (syn_cin R syntaxClass0003)
  let syntaxClass0005 : Class :=
    (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  let syntaxClass0006 : Class := (syn_cin S syntaxClass0005)
  let syntaxFormula0007 : Wff :=
    (syn_wiso (.cv f) syntaxClass0004 syntaxClass0006
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  let syntaxClass0008 : Class :=
    (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  let syntaxClass0009 : Class := (syn_cin R syntaxClass0008)
  let syntaxClass0010 : Class :=
    (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  let syntaxClass0011 : Class := (syn_cin S syntaxClass0010)
  let syntaxFormula0012 : Wff :=
    (syn_wiso (.cv g) syntaxClass0009 syntaxClass0011
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  let syntaxFormula0013 : Wff := (syn_wa syntaxFormula0007 syntaxFormula0012)
  let syntaxFormula0014 : Wff := (syn_wa syntaxFormula0002 syntaxFormula0013)
  let syntaxFormula0015 : Wff :=
    (syn_wa (.classEq (.cv z) (syn_cfv (.cv g) (.cv x))) syntaxFormula0014)
  let syntaxFormula0016 : Wff := (syn_wex z syntaxFormula0015)
  let syntaxClass0017 : Class :=
    (syn_cres (.cv g)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0018 : Wff := (.classMem syntaxClass0017 (syn_cvv))
  let syntaxFormula0019 : Wff :=
    (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E)) syntaxFormula0001)
  let syntaxFormula0020 : Wff := (syn_wa syntaxFormula0019 syntaxFormula0012)
  let syntaxFormula0021 : Wff :=
    (syn_wa syntaxFormula0020 (.classEq (.cv z) (syn_cfv (.cv g) (.cv x))))
  let syntaxClass0022 : Class :=
    (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))
  let syntaxClass0023 : Class := (syn_cin S syntaxClass0022)
  let syntaxFormula0024 : Wff :=
    (syn_wiso syntaxClass0017 syntaxClass0004 syntaxClass0023
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))
  let syntaxFormula0025 : Wff :=
    (syn_wf1o (.cv g) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  let syntaxFormula0026 : Wff :=
    (syn_wf (.cv g) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  let syntaxFormula0027 : Wff := (syn_wa syntaxFormula0026 syntaxFormula0001)
  let syntaxFormula0028 : Wff :=
    (.classMem (syn_cfv (.cv g) (.cv x))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  let syntaxFormula0029 : Wff :=
    (.classMem (.cv z)
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
  let syntaxFormula0030 : Wff := (syn_wb syntaxFormula0029 syntaxFormula0028)
  let syntaxClass0031 : Class := (syn_ccom syntaxClass0017 (syn_ccnv (.cv f)))
  let syntaxFormula0032 : Wff := (.classMem syntaxClass0031 (syn_cvv))
  let syntaxFormula0033 : Wff :=
    (syn_wiso (syn_ccnv (.cv f)) syntaxClass0006 syntaxClass0004
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0034 : Wff := (syn_wa syntaxFormula0033 syntaxFormula0024)
  let syntaxFormula0035 : Wff :=
    (syn_wiso syntaxClass0031 syntaxClass0006 syntaxClass0023
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))
  let syntaxFormula0036 : Wff :=
    (syn_wa (syn_wa (.classMem (.cv u) E) (.classMem (.cv z) E)) syntaxFormula0032)
  let syntaxFormula0037 : Wff := (syn_wa syntaxFormula0036 syntaxFormula0035)
  let syntaxFormula0038 : Wff :=
    (syn_wiso syntaxClass0017 syntaxClass0004 syntaxClass0006
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))))
  let syntaxFormula0039 : Wff :=
    (syn_wiso syntaxClass0017 syntaxClass0004 syntaxClass0006
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  let syntaxFormula0040 : Wff := (syn_wa syntaxFormula0007 syntaxFormula0039)
  let syntaxFormula0041 : Wff := (.classEq (.cv f) syntaxClass0017)
  have p0000 := @g_fvex (.cv x) (.cv g)
  have p0001 := @g_biid syntaxFormula0014
  have p0002 :=
    @g_a1i (syn_wb syntaxFormula0014 syntaxFormula0014)
      (.classEq (.cv z) (syn_cfv (.cv g) (.cv x))) p0001
  have p0003 :=
    @g_ceqsexv syntaxFormula0014 syntaxFormula0014 z (syn_cfv (.cv g) (.cv x))
      dv_cache_0001 dv_cache_0002 p0000 p0002
  have p0004 := @g_biimpri syntaxFormula0016 syntaxFormula0014 p0003
  have p0005 := @g_vex f
  have p0006 := @g_a1i (.classMem (.cv f) (syn_cvv)) syntaxFormula0015 p0005
  have p0007 := @g_vex g
  have p0008 := @g_brex R D (syn_cwe)
  have p0009 := Nominal.mp hyp_wecutisocompatndv_1 p0008
  have p0010 := @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0011 := Nominal.mp p0009 p0010
  have p0014 := @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0015 := Nominal.mp p0009 p0014
  have p0016 := @g_idex
  have p0017 := @g_difex R (syn_cid) p0015 p0016
  have p0018 := @g_cnvex (syn_cdif R (syn_cid)) p0017
  have p0019 := @g_snex (.cv x)
  have p0020 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0018 p0019
  have p0021 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0011 p0020
  have p0022 :=
    @g_resex (.cv g)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0007
      p0021
  have p0023 := @g_a1i syntaxFormula0018 syntaxFormula0015 p0022
  have p0024 :=
    @g_jca syntaxFormula0015 (.classMem (.cv f) (syn_cvv)) syntaxFormula0018 p0006 p0023
  have p0025 := @g_simpr (.classEq (.cv z) (syn_cfv (.cv g) (.cv x))) syntaxFormula0014
  have p0026 := @g_simpr syntaxFormula0002 syntaxFormula0013
  have p0027 := @g_simpl syntaxFormula0007 syntaxFormula0012
  have p0028 := @g_syl syntaxFormula0014 syntaxFormula0013 syntaxFormula0007 p0026 p0027
  have p0029 := @g_syl syntaxFormula0015 syntaxFormula0014 syntaxFormula0007 p0025 p0028
  have p0031 := @g_simpl syntaxFormula0002 syntaxFormula0013
  have p0032 := @g_simpl syntaxFormula0000 syntaxFormula0001
  have p0033 := @g_syl syntaxFormula0014 syntaxFormula0002 syntaxFormula0000 p0031 p0032
  have p0034 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))
  have p0035 :=
    @g_syl syntaxFormula0014 syntaxFormula0000
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) p0033 p0034
  have p0036 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0037 :=
    @g_syl syntaxFormula0014 (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classMem (.cv y) D) p0035 p0036
  have p0038 :=
    @g_syl syntaxFormula0015 syntaxFormula0014 (.classMem (.cv y) D) p0025 p0037
  have p0043 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))
  have p0044 :=
    @g_syl syntaxFormula0014 syntaxFormula0000
      (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E)) p0033 p0043
  have p0045 := @g_simpr (.classMem (.cv u) E) (.classMem (.cv v) E)
  have p0046 :=
    @g_syl syntaxFormula0014 (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))
      (.classMem (.cv v) E) p0044 p0045
  have p0047 :=
    @g_syl syntaxFormula0015 syntaxFormula0014 (.classMem (.cv v) E) p0025 p0046
  have p0048 :=
    @g_jca syntaxFormula0015 (.classMem (.cv y) D) (.classMem (.cv v) E) p0038 p0047
  have p0051 := @g_simpr syntaxFormula0000 syntaxFormula0001
  have p0052 := @g_syl syntaxFormula0014 syntaxFormula0002 syntaxFormula0001 p0031 p0051
  have p0053 := @g_syl syntaxFormula0015 syntaxFormula0014 syntaxFormula0001 p0025 p0052
  have p0054 :=
    @g_jca syntaxFormula0015 (syn_wa (.classMem (.cv y) D) (.classMem (.cv v) E))
      syntaxFormula0001 p0048 p0053
  have p0057 := @g_simpr syntaxFormula0007 syntaxFormula0012
  have p0058 := @g_syl syntaxFormula0014 syntaxFormula0013 syntaxFormula0012 p0026 p0057
  have p0059 := @g_syl syntaxFormula0015 syntaxFormula0014 syntaxFormula0012 p0025 p0058
  have p0060 := @g_jca syntaxFormula0015 syntaxFormula0019 syntaxFormula0012 p0054 p0059
  have p0061 := @g_simpl (.classEq (.cv z) (syn_cfv (.cv g) (.cv x))) syntaxFormula0014
  have p0062 :=
    @g_jca syntaxFormula0015 syntaxFormula0020
      (.classEq (.cv z) (syn_cfv (.cv g) (.cv x))) p0060 p0061
  have p0063 :=
    @g_isocutstrictsegresndv x y z v D R S E (.cv g) hyp_wecutisocompatndv_1
      hyp_wecutisocompatndv_2
  have p0064 := @g_syl syntaxFormula0015 syntaxFormula0021 syntaxFormula0024 p0062 p0063
  have p0071 := @g_simpl (.classMem (.cv u) E) (.classMem (.cv v) E)
  have p0072 :=
    @g_syl syntaxFormula0014 (syn_wa (.classMem (.cv u) E) (.classMem (.cv v) E))
      (.classMem (.cv u) E) p0044 p0071
  have p0073 :=
    @g_syl syntaxFormula0015 syntaxFormula0014 (.classMem (.cv u) E) p0025 p0072
  have p0079 :=
    @g_isof1o (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
      syntaxClass0009 syntaxClass0011 (.cv g)
  have p0080 :=
    @g_f1of (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (.cv g)
  have p0081 := @g_syl syntaxFormula0012 syntaxFormula0025 syntaxFormula0026 p0079 p0080
  have p0082 := @g_syl syntaxFormula0015 syntaxFormula0012 syntaxFormula0026 p0059 p0081
  have p0088 := @g_jca syntaxFormula0015 syntaxFormula0026 syntaxFormula0001 p0082 p0053
  have p0089 :=
    @g_ffvelrn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) (.cv x)
      (.cv g)
  have p0090 := @g_syl syntaxFormula0015 syntaxFormula0027 syntaxFormula0028 p0088 p0089
  have p0092 :=
    @g_eleq1 (.cv z) (syn_cfv (.cv g) (.cv x))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))
  have p0093 :=
    @g_syl syntaxFormula0015 (.classEq (.cv z) (syn_cfv (.cv g) (.cv x)))
      syntaxFormula0030 p0061 p0092
  have p0094 :=
    @g_mpbird syntaxFormula0015 syntaxFormula0029 syntaxFormula0028 p0090 p0093
  have p0095 := @g_inss1 E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))
  have p0096 :=
    @g_sseli (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))) E
      (.cv z) p0095
  have p0097 :=
    @g_syl syntaxFormula0015 syntaxFormula0029 (.classMem (.cv z) E) p0094 p0096
  have p0098 :=
    @g_jca syntaxFormula0015 (.classMem (.cv u) E) (.classMem (.cv z) E) p0073 p0097
  have p0116 := @g_cnvex (.cv f) p0005
  have p0117 := @g_coex syntaxClass0017 (syn_ccnv (.cv f)) p0022 p0116
  have p0118 := @g_a1i syntaxFormula0032 syntaxFormula0015 p0117
  have p0119 :=
    @g_jca syntaxFormula0015 (syn_wa (.classMem (.cv u) E) (.classMem (.cv z) E))
      syntaxFormula0032 p0098 p0118
  have p0125 :=
    @g_isocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      syntaxClass0004 syntaxClass0006 (.cv f)
  have p0126 := @g_syl syntaxFormula0015 syntaxFormula0007 syntaxFormula0033 p0029 p0125
  have p0162 := @g_jca syntaxFormula0015 syntaxFormula0033 syntaxFormula0024 p0126 p0064
  have p0163 :=
    @g_isotr (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
      syntaxClass0006 syntaxClass0004 syntaxClass0023 syntaxClass0017 (syn_ccnv (.cv f))
  have p0164 := @g_syl syntaxFormula0015 syntaxFormula0034 syntaxFormula0035 p0162 p0163
  have p0165 := @g_jca syntaxFormula0015 syntaxFormula0036 syntaxFormula0035 p0119 p0164
  have p0166 := @g_wecutisoendpointseqndv u z E S syntaxClass0031 hyp_wecutisocompatndv_2
  have p0167 :=
    @g_syl syntaxFormula0015 syntaxFormula0037 (.classEq (.cv u) (.cv z)) p0165 p0166
  have p0168 := @g_sneq (.cv u) (.cv z)
  have p0169 :=
    @g_syl syntaxFormula0015 (.classEq (.cv u) (.cv z))
      (.classEq (syn_csn (.cv u)) (syn_csn (.cv z))) p0167 p0168
  have p0170 :=
    @g_imaeq2d syntaxFormula0015 (syn_csn (.cv u)) (syn_csn (.cv z))
      (syn_ccnv (syn_cdif S (syn_cid))) p0169
  have p0171 :=
    @g_ineq2d syntaxFormula0015
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))) E p0170
  have p0279 :=
    @g_xpeq12d syntaxFormula0015
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))) p0171
      p0171
  have p0280 := @g_ineq2d syntaxFormula0015 syntaxClass0005 syntaxClass0022 S p0279
  have p0281 := @g_eqcomd syntaxFormula0015 syntaxClass0006 syntaxClass0023 p0280
  have p0282 :=
    @g_isoeq3 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
      syntaxClass0004 syntaxClass0023 syntaxClass0006 syntaxClass0017
  have p0283 :=
    @g_syl syntaxFormula0015 (.classEq syntaxClass0023 syntaxClass0006)
      (syn_wb syntaxFormula0024 syntaxFormula0038) p0281 p0282
  have p0284 := @g_mpbid syntaxFormula0015 syntaxFormula0024 syntaxFormula0038 p0064 p0283
  have p0392 :=
    @g_eqcomd syntaxFormula0015
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z)))) p0171
  have p0393 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      syntaxClass0004 syntaxClass0006 syntaxClass0017
  have p0394 :=
    @g_syl syntaxFormula0015
      (.classEq (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv z))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wb syntaxFormula0038 syntaxFormula0039) p0392 p0393
  have p0395 := @g_mpbid syntaxFormula0015 syntaxFormula0038 syntaxFormula0039 p0284 p0394
  have p0396 := @g_jca syntaxFormula0015 syntaxFormula0007 syntaxFormula0039 p0029 p0395
  have p0397 :=
    @g_jca syntaxFormula0015 (syn_wa (.classMem (.cv f) (syn_cvv)) syntaxFormula0018)
      syntaxFormula0040 p0024 p0396
  have p0398 :=
    @g_wecutisouniquecl (.cv x) (.cv u) D R S E (.cv f) syntaxClass0017
      hyp_wecutisocompatndv_1 hyp_wecutisocompatndv_2
  have p0399 :=
    @g_syl syntaxFormula0015
      (syn_wa (syn_wa (.classMem (.cv f) (syn_cvv)) syntaxFormula0018) syntaxFormula0040)
      syntaxFormula0041 p0397 p0398
  have p0400 := @g_exlimiv syntaxFormula0015 syntaxFormula0041 z dv_cache_0003 p0399
  have p0401 := @g_syl syntaxFormula0014 syntaxFormula0016 syntaxFormula0041 p0004 p0400
  exact p0401


end NFChoice.DirectNominalPrf.WPPReplay

end
