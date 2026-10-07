/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part027`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodepartsndv`. -/
@[expose]
noncomputable def gHnwcutcodepartsndv (x : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq
            (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
                (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn (.cv x))))))) (.classEq (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))))) :=
  by
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0001 :=
    @gIftrue (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A))
      (.classEq (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (.cv u))
      p0000 p0001
  have p0003 :=
    @gFveq2d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (.cv u) (synC1st) p0002
  have p0007 :=
    @gFveq2d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (.cv u) (synC2nd) p0002
  have p0008 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC1st) (.cv u)))
      (.classEq (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (.cv u)))
      p0003 p0007
  have p0009 :=
    @gHnwcutcodeeq12ndv x
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (.cv u))) (.classEq (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (.cv u))))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0008 p0009
  have p0011 :=
    @gFveq2d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synC1st) p0010
  have p0012 :=
    @gEqcomd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0011
  have p0013 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0018 :=
    @gEleq2d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC2nd) (.cv u)) (.cv x) p0007
  have p0019 :=
    @gMpbird
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0013 p0018
  have p0020 := @gHncodetotalleftmemndv u A dv_cache_0001
  have p0021 :=
    @gHwcnweclndv A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gWecutisogencodeparts x
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0022
  have p0024 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWa (.classEq (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCin (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x))))))) (.classEq
          (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      p0019 p0023
  have p0025 :=
    @gSimpld
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      p0024
  have p0038 :=
    @gDifeq1d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (.cv u)) (synCid) p0003
  have p0039 :=
    @gCnveqd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCdif (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCid))
      (synCdif (synCfv (synC1st) (.cv u)) (synCid)) p0038
  have p0040 :=
    @gImaeq1d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCcnv (synCdif (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCid)))
      (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn (.cv x)) p0039
  have p0041 :=
    @gIneq12d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC2nd) (.cv u))
      (synCima (synCcnv (synCdif (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn (.cv x)))
      p0007 p0040
  have p0054 :=
    @gXpeq12d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      p0041 p0041
  have p0055 :=
    @gIneq12d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (.cv u))
      (synCxp (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0003 p0054
  have p0056 :=
    @gN3eqtrd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCin (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCxp (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0012 p0025 p0055
  have p0068 :=
    @gFveq2d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synC2nd) p0010
  have p0069 :=
    @gEqcomd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0068
  have p0082 :=
    @gSimprd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      p0024
  have p0095 :=
    @gN3eqtrd
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      p0069 p0082 p0041
  have p0096 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0056 p0095
  exact p0096

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeambientclndv`. -/
@[expose]
noncomputable def gHnwcutcodeambientclndv (u : Var) (A : Class) (B : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem B (synCfv (synC2nd) (.cv u)))) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
          (synChwcn A))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ u from (by exact fresh_x_ne_u)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCfv (synC2nd) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((Wff.imp (.classMem (.cv u) (synChwcn A)) (.classMem
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
            (synChwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, fresh_x_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gHnwcutcodeeq3 (.cv x) B (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
      dv_cache_0001
  have p0001 :=
    @gEleq1
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
      (synChwcn A)
  have p0002 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
      (synWb (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
          (synChwcn A)))
      p0000 p0001
  have p0003 :=
    @gImbi2d (.classEq (.cv x) B)
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
        (synChwcn A))
      (.classMem (.cv u) (synChwcn A)) p0002
  have p0004 := @gHnwcutcodeambientndv x u A dv_cache_0002
  have p0005 :=
    @gExpcom (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0004
  have p0006 :=
    @gVtoclga
      (.imp (.classMem (.cv u) (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)))
      (.imp (.classMem (.cv u) (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
          (synChwcn A)))
      x B (synCfv (synC2nd) (.cv u)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0003
      p0005
  have p0007 :=
    @gImpcom (.classMem B (synCfv (synC2nd) (.cv u))) (.classMem (.cv u) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
        (synChwcn A))
      p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part028`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodepartsclndv`. -/
@[expose]
noncomputable def gHnwcutcodepartsclndv (u : Var) (A : Class) (B : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem B (synCfv (synC2nd) (.cv u)))) (synWa (.classEq (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
            (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn B))) (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn B)))))) (.classEq (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn B)))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ u from (by exact fresh_x_ne_u)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCfv (synC2nd) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((Wff.imp (.classMem (.cv u) (synChwcn A)) (synWa (.classEq (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
              (synCin (synCfv (synC1st) (.cv u)) (synCxp
                  (synCin (synCfv (synC2nd) (.cv u))
                    (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                      (synCsn B))) (synCin (synCfv (synC2nd) (.cv u))
                    (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                      (synCsn B)))))) (.classEq (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn B))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, fresh_x_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gHnwcutcodeeq3 (.cv x) B (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
      dv_cache_0001
  have p0001 :=
    @gFveq2d (.classEq (.cv x) B)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
      (synC1st) p0000
  have p0002 := @gId (.classEq (.cv x) B)
  have p0003 := @gSneqd (.classEq (.cv x) B) (.cv x) B p0002
  have p0004 :=
    @gImaeq2d (.classEq (.cv x) B) (synCsn (.cv x)) (synCsn B)
      (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) p0003
  have p0005 :=
    @gIneq2
      (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B))
      (synCfv (synC2nd) (.cv u))
  have p0006 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x)))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B)))
      (.classEq (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B))))
      p0004 p0005
  have p0012 :=
    @gXpeq12d (.classEq (.cv x) B)
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B)))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B)))
      p0006 p0006
  have p0013 :=
    @gIneq2
      (synCxp (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      (synCxp (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B))))
      (synCfv (synC1st) (.cv u))
  have p0014 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn B)))))
      (.classEq (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn B))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn B))))))
      p0012 p0013
  have p0015 :=
    @gEqeq12d (.classEq (.cv x) B)
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn B)))))
      p0001 p0014
  have p0017 :=
    @gFveq2d (.classEq (.cv x) B)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
      (synC2nd) p0000
  have p0023 :=
    @gEqeq12d (.classEq (.cv x) B)
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B)))
      p0017 p0006
  have p0024 :=
    @gAnbi12d (.classEq (.cv x) B)
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn B))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn B))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid))) (synCsn B))))
      p0015 p0023
  have p0025 :=
    @gImbi2d (.classEq (.cv x) B)
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn B))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn B)))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn B)))))
      (.classMem (.cv u) (synChwcn A)) p0024
  have p0026 := @gHnwcutcodepartsndv x u A dv_cache_0002
  have p0027 :=
    @gExpcom (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0026
  have p0028 :=
    @gVtoclga
      (.imp (.classMem (.cv u) (synChwcn A)) (synWa (.classEq (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
                (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn (.cv x))))))) (.classEq (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.imp (.classMem (.cv u) (synChwcn A)) (synWa (.classEq (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
            (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn B))) (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn B)))))) (.classEq (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn B))))))
      x B (synCfv (synC2nd) (.cv u)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0025
      p0027
  have p0029 :=
    @gImpcom (.classMem B (synCfv (synC2nd) (.cv u))) (.classMem (.cv u) (synChwcn A))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn B))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn B)))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn B)))))
      p0028
  exact p0029


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part029`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeisoimagendv`. -/
@[expose]
noncomputable def gHnwcutcodeisoimagendv (x : Var) (v : Var) (u : Var) (A : Class)
    (h : Var) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪
      ({ h } : Finset Var)
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_ne_x : g ≠ x := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_v : g ≠ v := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_u : g ≠ u := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_ne_h : g ≠ h := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0003 :
    g ∉
      ((synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_h, fresh_g_ne_u, fresh_g_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 :
    g ∉
      ((synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          Finset.mem_union, Finset.mem_singleton, fresh_g_ne_x, fresh_g_ne_u,
          fresh_g_ne_h, fresh_g_ne_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : g ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_A, not_false_eq_true])
  have dv_cache_0006 :
    g ∉
      ((synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_x, fresh_g_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 :
    g ∉
      ((synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_x, fresh_g_ne_h, fresh_g_ne_v,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0001 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0000
  have p0003 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0000
  have p0004 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0001 p0003
  have p0005 :=
    @gIsostrictsegresndv x (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
      (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv h)
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      p0004 p0005
  have p0007 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0008 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0007
  have p0011 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      p0008 p0003
  have p0012 := @gHnwcutcodepartsndv x u A dv_cache_0001
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0011 p0012
  have p0014 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0013
  have p0015 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0014
  have p0016 :=
    @gIsoeq2
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (synCfv (.cv h) (.cv x)))))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWb (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
              (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))) (synWiso (synCres (.cv h)
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))))
      p0015 p0016
  have p0019 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0007
  have p0022 :=
    @gIsof1o (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (.cv h)
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWf1o (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))) p0001
      p0022
  have p0024 := @gF1of (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv h)
  have p0025 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWf1o (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWf (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))) p0023
      p0024
  have p0028 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWf (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0025 p0003
  have p0029 :=
    @gFfvelrn (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv x) (.cv h)
  have p0030 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v))) p0028 p0029
  have p0031 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv v) (synChwcn A))
      (.classMem (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v))) p0019 p0030
  have p0032 := @gHnwcutcodepartsclndv v A (synCfv (.cv h) (.cv x)) dv_cache_0002
  have p0033 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
              (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (synCfv (.cv h) (.cv x)))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))))
      p0031 p0032
  have p0034 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      p0033
  have p0035 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))))
      p0034
  have p0036 :=
    @gIsoeq3
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (synCfv (.cv h) (.cv x)))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
  have p0037 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))))
      (synWb (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))) (synWiso (synCres (.cv h)
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))))
      p0035 p0036
  have p0038 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      p0017 p0037
  have p0046 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0013
  have p0047 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      p0046
  have p0048 :=
    @gIsoeq4
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (synCfv (.cv h) (.cv x)))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
  have p0049 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWb (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))) (synWiso (synCres (.cv h)
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))))
      p0047 p0048
  have p0050 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      p0038 p0049
  have p0067 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      p0033
  have p0068 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (synCfv (.cv h) (.cv x)))))
      p0067
  have p0069 :=
    @gIsoeq5
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (synCfv (.cv h) (.cv x)))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
  have p0070 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))))
      (synWb (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (synCfv (.cv h) (.cv x)))))) (synWiso (synCres (.cv h)
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x))))))
      p0068 p0069
  have p0071 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))))
      p0050 p0070
  have p0072 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (synCfv (.cv h) (.cv x))))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (synCfv (.cv h) (.cv x))))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))))
      p0006 p0071
  have p0073 := @gVex h
  have p0074 :=
    @gA1i (.classMem (.cv h) (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      p0073
  have p0075 :=
    @gFvex
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synC2nd)
  have p0076 :=
    @gA1i
      (.classMem (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      p0075
  have p0085 :=
    @gEleq1d
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCvv) p0046
  have p0086 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCvv))
      (.classMem (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCvv))
      p0076 p0085
  have p0087 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv h) (synCvv))
      (.classMem (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (synCvv))
      p0074 p0086
  have p0088 :=
    @gResexg (.cv h)
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (synCvv) (synCvv)
  have p0089 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv h) (synCvv)) (.classMem (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCvv)))
      (.classMem (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCvv))
      p0087 p0088
  have p0090 :=
    @gIsoeq1
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      (.cv g)
  have p0091 :=
    @gSpcegv
      (synWiso (.cv g) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))))
      g
      (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      (synCvv) dv_cache_0003 dv_cache_0004 p0090
  have p0092 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCvv))
      (.imp (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x))))) (synWex g (synWiso (.cv g) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (synCfv (.cv h) (.cv x)))))))
      p0089 p0091
  have p0093 :=
    @gMpd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (synCres (.cv h) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))))
      (synWex g (synWiso (.cv g) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x))))))
      p0072 p0092
  have p0099 := @gHnwcutcodeambientndv x u A dv_cache_0001
  have p0100 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0011 p0099
  have p0115 := @gHnwcutcodeambientclndv v A (synCfv (.cv h) (.cv x)) dv_cache_0002
  have p0116 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))) (synChwcn A))
      p0031 p0115
  have p0117 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))) (synChwcn A))
      p0100 p0116
  have p0118 :=
    @gHwnisodirectisobclndv A
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
        (synCfv (.cv h) (.cv x)))
      g dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0119 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x))) (synChwcn A)))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))) (synWex g (synWiso (.cv g) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (synCfv (.cv h) (.cv x)))))))
      p0117 p0118
  have p0120 :=
    @gBiimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      (synWex g (synWiso (.cv g) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x))))))
      p0119
  have p0121 :=
    @gMpd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWex g (synWiso (.cv g) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x)))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (synCfv (.cv h) (.cv x))))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      p0093 p0120
  exact p0121


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part030`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodetransportndv`. -/
@[expose]
noncomputable def gHnwcutcodetransportndv (x : Var) (y : Var) (v : Var) (u : Var)
    (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_u_y : u ≠ y) (dv_v_y : v ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
        (synWrex y (synCfv (synC2nd) (.cv v)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv y))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ v } : Finset Var) ∪
        ({ u } : Finset Var) ∪
      A.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_x : h ≠ x := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_h_ne_y : h ≠ y := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_h : y ≠ h := Ne.symm fresh_h_ne_y
  have fresh_h_ne_v : h ≠ v := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : h ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_u, not_false_eq_true])
  have dv_cache_0003 : h ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_v, not_false_eq_true])
  have dv_cache_0004 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0005 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0006 : Disjoint ((Class.cv y)).fv ((synCfv (synC1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((Class.cv y)).fv ((synCfv (synC1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ y } : Finset Var)) ((((Class.cv v)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ y } : Finset Var)) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ y } : Finset Var)) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show y ∉ ({ v } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show y ≠ v from (by exact Ne.symm dv_v_y)))))))),
                  (show Disjoint (({ y } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ y } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0007 : y ∉ ((synCfv (.cv h) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_h, or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synCfv (synC2nd) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_y), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), (Ne.symm dv_u_y), fresh_y_ne_h,
          (Ne.symm dv_v_y), dv_A_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    h ∉
      ((synWrex y (synCfv (synC2nd) (.cv v)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_h_ne_v, fresh_h_ne_x,
          fresh_h_ne_u, fresh_h_ne_y, fresh_h_not_A, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0011 :
    h ∉
      ((synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, fresh_h_not_A, fresh_h_ne_v, fresh_h_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0001 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0000
  have p0002 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0003 :=
    @gHwnisodirectisobclndv A (.cv u) (.cv v) h dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0002 p0003
  have p0005 :=
    @gBiimpd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0004
  have p0006 :=
    @gMpd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0001 p0005
  have p0009 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0000
  have p0010 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0002 p0009
  have p0011 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
  have p0012 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0011
  have p0013 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
  have p0015 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0011
  have p0016 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0013 p0015
  have p0017 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0012 p0016
  have p0018 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0019 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0018
  have p0020 :=
    @gIsof1o (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (.cv h)
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWf1o (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))) p0019
      p0020
  have p0022 := @gF1of (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv h)
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWf1o (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWf (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))) p0021
      p0022
  have p0025 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0018
  have p0026 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWf (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0023 p0025
  have p0027 :=
    @gFfvelrn (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv x) (.cv h)
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf (.cv h) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v))) p0026 p0027
  have p0029 := @gHnwcutcodeisoimagendv x v u A h dv_cache_0004 dv_cache_0005
  have p0030 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      p0028 p0029
  have p0031 :=
    @gHnwcutcodeeq3 (.cv y) (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv v)) dv_cache_0006
  have p0032 :=
    @gBreq2d (.classEq (.cv y) (synCfv (.cv h) (.cv x)))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
        (synCfv (.cv h) (.cv x)))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A) p0031
  have p0033 :=
    @gRspcev
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (synCfv (.cv h) (.cv x))))
      y (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v)) dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0032
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (synCfv (.cv h) (.cv x)) (synCfv (synC2nd) (.cv v))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (synCfv (.cv h) (.cv x)))))
      (synWrex y (synCfv (synC2nd) (.cv v)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      p0030 p0033
  have p0035 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWrex y (synCfv (synC2nd) (.cv v)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      p0017 p0034
  have p0036 :=
    @gEx
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWrex y (synCfv (synC2nd) (.cv v)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      p0035
  have p0037 :=
    @gExlimdv
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWrex y (synCfv (synC2nd) (.cv v)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      h dv_cache_0010 dv_cache_0011 p0036
  have p0038 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.imp (synWex h
          (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (synWrex y (synCfv (synC2nd) (.cv v)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv y)))))
      p0010 p0037
  have p0039 :=
    @gMpd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWrex y (synCfv (synC2nd) (.cv v)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      p0006 p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodetransporttgtclndv`. -/
@[expose]
noncomputable def gHnwcutcodetransporttgtclndv (x : Var) (y : Var) (u : Var) (A : Class)
    (C : Class) (dv_A_u : u ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_C_y : y ∉ C.fv)
    (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
          (synWa (synWbr (.cv u) (synChwniso A) C)
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
        (synWrex y (synCfv (synC2nd) C) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ C.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((synCfv (synC2nd) (.cv w))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCfv (synC2nd) C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_C_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv w) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, dv_C_y, or_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0005 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0006 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0007 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show u ≠ y from (by exact dv_u_y))
  have dv_cache_0008 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0010 : w ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_w_not_A, not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((Wff.imp (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (synWbr (.cv u) (synChwniso A) C)
              (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
          (synWrex y (synCfv (synC2nd) C) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_u, fresh_w_not_A,
          fresh_w_not_C, fresh_w_ne_x, fresh_w_ne_y, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
      (synWa (synWbr (.cv u) (synChwniso A) C)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0001 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) C)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)) p0000
  have p0002 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
      (synWa (synWbr (.cv u) (synChwniso A) C)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0003 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) C)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A))
      (synWa (synWbr (.cv u) (synChwniso A) C)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0001 p0002
  have p0005 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) C)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)) p0000
  have p0006 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) C)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (synWa (synWbr (.cv u) (synChwniso A) C)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem C (synChwcn A)) p0003 p0005
  have p0007 := @gBiidd (.classEq (.cv w) C) (.classMem (.cv u) (synChwcn A))
  have p0008 := @gId (.classEq (.cv w) C)
  have p0009 := @gBreq2d (.classEq (.cv w) C) (.cv w) C (.cv u) (synChwniso A) p0008
  have p0010 :=
    @gBiidd (.classEq (.cv w) C) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0011 :=
    @gAnbi12d (.classEq (.cv w) C) (synWbr (.cv u) (synChwniso A) (.cv w))
      (synWbr (.cv u) (synChwniso A) C) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0009 p0010
  have p0012 :=
    @gAnbi12d (.classEq (.cv w) C) (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synChwcn A))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (synWbr (.cv u) (synChwniso A) C)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0007 p0011
  have p0014 := @gFveq2d (.classEq (.cv w) C) (.cv w) C (synC2nd) p0008
  have p0016 := @gFveq2d (.classEq (.cv w) C) (.cv w) C (synC1st) p0008
  have p0019 :=
    @gJca (.classEq (.cv w) C)
      (.classEq (synCfv (synC1st) (.cv w)) (synCfv (synC1st) C))
      (.classEq (synCfv (synC2nd) (.cv w)) (synCfv (synC2nd) C)) p0016 p0014
  have p0020 :=
    @gHnwcutcodeeq12ndv y (synCfv (synC2nd) (.cv w)) (synCfv (synC1st) (.cv w))
      (synCfv (synC1st) C) (synCfv (synC2nd) C)
  have p0021 :=
    @gSyl (.classEq (.cv w) C)
      (synWa (.classEq (synCfv (synC1st) (.cv w)) (synCfv (synC1st) C))
        (.classEq (synCfv (synC2nd) (.cv w)) (synCfv (synC2nd) C)))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
          (.cv y)) (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y)))
      p0019 p0020
  have p0022 :=
    @gBreq2d (.classEq (.cv w) C)
      (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))
      (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A) p0021
  have p0023 :=
    @gRexeqbidv (.classEq (.cv w) C)
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y)))
      y (synCfv (synC2nd) (.cv w)) (synCfv (synC2nd) C) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0014 p0022
  have p0024 :=
    @gImbi12d (.classEq (.cv w) C)
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (synWa (synWbr (.cv u) (synChwniso A) C)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
      (synWrex y (synCfv (synC2nd) C) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y))))
      p0012 p0023
  have p0025 :=
    @gSimpr (.classMem (.cv w) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
  have p0026 :=
    @gSimpld
      (synWa (.classMem (.cv w) (synChwcn A)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0025
  have p0027 :=
    @gSimpl (.classMem (.cv w) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
  have p0028 :=
    @gJca
      (synWa (.classMem (.cv w) (synChwcn A)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0026 p0027
  have p0030 :=
    @gSimprd
      (synWa (.classMem (.cv w) (synChwcn A)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0025
  have p0031 :=
    @gJca
      (synWa (.classMem (.cv w) (synChwcn A)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0028 p0030
  have p0032 :=
    @gHnwcutcodetransportndv x y w u A dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0033 :=
    @gSyl
      (synWa (.classMem (.cv w) (synChwcn A)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
      p0031 p0032
  have p0034 :=
    @gEx (.classMem (.cv w) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w)) (.cv y))))
      p0033
  have p0035 :=
    @gVtoclga
      (.imp (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (synWbr (.cv u) (synChwniso A) (.cv w))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
        (synWrex y (synCfv (synC2nd) (.cv w)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv w))
              (.cv y)))))
      (.imp (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (synWbr (.cv u) (synChwniso A) C)
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
        (synWrex y (synCfv (synC2nd) C) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y)))))
      w C (synChwcn A) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0024 p0034
  have p0036 :=
    @gImpcom (.classMem C (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcn A)) (synWa (synWbr (.cv u) (synChwniso A) C)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWrex y (synCfv (synC2nd) C) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y))))
      p0035
  have p0037 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
        (synWa (synWbr (.cv u) (synChwniso A) C)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (synWbr (.cv u) (synChwniso A) C)
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (.classMem C (synChwcn A)))
      (synWrex y (synCfv (synC2nd) C) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv y))))
      p0006 p0036
  exact p0037


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part031`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodetransportintocutndv`. -/
@[expose]
noncomputable def gHnwcutcodetransportintocutndv (x : Var) (y : Var) (z : Var) (v : Var)
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_u_z : u ≠ z) (dv_v_z : v ≠ z) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
        (synWrex z (synCfv (synC2nd) (.cv v)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ({ v } : Finset Var) ∪
        ({ u } : Finset Var) ∪
      A.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_ne_v : w ≠ v := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_w : u ≠ w := Ne.symm fresh_w_ne_u
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0004 :
    w ∉
      ((synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0006 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0007 : Disjoint ((Class.cv z)).fv ((synCfv (synC1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv z)).fv ((synCfv (synC1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var)) ((((Class.cv v)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ z } : Finset Var)) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ z } : Finset Var)) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show z ∉ ({ v } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show z ≠ v from (by exact Ne.symm dv_v_z)))))))),
                  (show Disjoint (({ z } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ z } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0008 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synCfv (synC2nd) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_z), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    z ∉
      ((synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), (Ne.symm dv_u_z), fresh_z_ne_w,
          (Ne.symm dv_v_z), dv_A_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    w ∉
      ((synWrex z (synCfv (synC2nd) (.cv v)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_v, fresh_w_ne_x,
          fresh_w_ne_u, fresh_w_ne_z, fresh_w_not_A, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_u, fresh_w_not_A, fresh_w_ne_v, fresh_w_ne_y,
          fresh_w_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0001 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv v))) p0000
  have p0002 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0001
  have p0005 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0001
  have p0007 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv v))) p0000
  have p0008 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))
      p0005 p0007
  have p0009 := @gHnwcutcodeambientndv y v A dv_cache_0001
  have p0010 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv y)) (synChwcn A))
      p0008 p0009
  have p0011 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv y)) (synChwcn A))
      p0002 p0010
  have p0012 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0013 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0012
  have p0015 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0012
  have p0016 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0013 p0015
  have p0017 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))
          (synChwcn A)))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0011 p0016
  have p0018 :=
    @gHnwcutcodetransporttgtclndv x w u A
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0019 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))
            (synChwcn A))) (synWa (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWrex w (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.cv w))))
      p0017 p0018
  have p0020 :=
    @gSimpr
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv w) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv y)))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.cv w))))
  have p0021 :=
    @gSimpld
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)))
      p0020
  have p0022 :=
    @gSimpl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv w) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv y)))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.cv w))))
  have p0029 := @gHnwcutcodepartsndv y v A dv_cache_0001
  have p0030 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))))
      p0008 p0029
  have p0031 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0022 p0031
  have p0033 :=
    @gEleq2d
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv y))))
      (.cv w) p0032
  have p0034 :=
    @gMpbid
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      (.classMem (.cv w) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0021 p0033
  have p0035 :=
    @gInss1 (synCfv (synC2nd) (.cv v))
      (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))) (synCsn (.cv y)))
  have p0036 :=
    @gSseli
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv y))))
      (synCfv (synC2nd) (.cv v)) (.cv w) p0035
  have p0037 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      (.classMem (.cv w) (synCfv (synC2nd) (.cv v))) p0034 p0036
  have p0039 :=
    @gSimprd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)))
      p0020
  have p0049 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0030
  have p0050 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))))
      p0022 p0049
  have p0062 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0050 p0032
  have p0063 :=
    @gHnwcutcodeeq12ndv w
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv y))))
  have p0064 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)) (synChnwcutcode (synCin (synCfv (synC1st) (.cv v)) (synCxp
              (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y)))) (.cv w)))
      p0062 p0063
  have p0069 := @gHwcnweclndv A (.cv v)
  have p0070 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv v) (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v))) p0005
      p0069
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v))) p0022
      p0070
  have p0075 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv v))) p0022 p0007
  have p0076 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv v))) p0071 p0075
  have p0092 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv w) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0076 p0034
  have p0093 :=
    @gHnwcutcodenestndv w y (synCfv (synC2nd) (.cv v)) (synCfv (synC1st) (.cv v))
  have p0094 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (.classMem (.cv w)
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))))
      (.classEq (synChnwcutcode (synCin (synCfv (synC1st) (.cv v)) (synCxp
              (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y)))) (.cv w))
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w)))
      p0092 p0093
  have p0095 :=
    @gEqtrd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.cv w))
      (synChnwcutcode (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))) (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w))
      p0064 p0094
  have p0096 :=
    @gBreq2d
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A) p0095
  have p0097 :=
    @gMpbid
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w)))
      p0039 p0096
  have p0098 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCfv (synC2nd) (.cv v)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w)))
      p0037 p0097
  have p0099 :=
    @gHnwcutcodeeq3 (.cv z) (.cv w) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv v)) dv_cache_0007
  have p0100 :=
    @gBreq2d (.classEq (.cv z) (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A) p0099
  have p0101 :=
    @gRspcev
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w)))
      z (.cv w) (synCfv (synC2nd) (.cv v)) dv_cache_0008 dv_cache_0009 dv_cache_0010
      p0100
  have p0102 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (.classMem (.cv w) (synCfv (synC2nd) (.cv v))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w))))
      (synWrex z (synCfv (synC2nd) (.cv v)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      p0098 p0101
  have p0103 :=
    @gRexlimddv
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)))
      (synWrex z (synCfv (synC2nd) (.cv v)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      w
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      dv_cache_0011 dv_cache_0012 p0019 p0102
  exact p0103


end NFChoice.DirectNominalPrf.WPPReplay

end
