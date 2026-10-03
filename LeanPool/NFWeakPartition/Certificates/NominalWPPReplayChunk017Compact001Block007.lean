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

@[expose]
noncomputable def g_hnwcutcodepartsndv (x : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq
            (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
                (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))))) :=
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
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0001 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (.cv u))
      p0000 p0001
  have p0003 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (.cv u) (syn_c1st) p0002
  have p0007 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (.cv u) (syn_c2nd) p0002
  have p0008 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c1st) (.cv u)))
      (.classEq (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (.cv u)))
      p0003 p0007
  have p0009 :=
    @g_hnwcutcodeeq12ndv x
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (.cv u))) (.classEq (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0008 p0009
  have p0011 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_c1st) p0010
  have p0012 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0011
  have p0013 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0018 :=
    @g_eleq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c2nd) (.cv u)) (.cv x) p0007
  have p0019 :=
    @g_mpbird
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0013 p0018
  have p0020 := @g_hncodetotalleftmemndv u A dv_cache_0001
  have p0021 :=
    @g_hwcnweclndv A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_wecutisogencodeparts x
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0022
  have p0024 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))) (.classEq
          (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      p0019 p0023
  have p0025 :=
    @g_simpld
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      p0024
  have p0038 :=
    @g_difeq1d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cid) p0003
  have p0039 :=
    @g_cnveqd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cid))
      (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)) p0038
  have p0040 :=
    @g_imaeq1d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cid)))
      (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)) p0039
  have p0041 :=
    @g_ineq12d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c2nd) (.cv u))
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))
      p0007 p0040
  have p0054 :=
    @g_xpeq12d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      p0041 p0041
  have p0055 :=
    @g_ineq12d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (.cv u))
      (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0003 p0054
  have p0056 :=
    @g_n_3eqtrd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0012 p0025 p0055
  have p0068 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_c2nd) p0010
  have p0069 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0068
  have p0082 :=
    @g_simprd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      p0024
  have p0095 :=
    @g_n_3eqtrd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      p0069 p0082 p0041
  have p0096 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0056 p0095
  exact p0096

@[expose]
noncomputable def g_hnwcutcodeambientclndv (u : Var) (A : Class) (B : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem B (syn_cfv (syn_c2nd) (.cv u)))) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
          (syn_chwcn A))) :=
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
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
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
                  (show Disjoint (({ x } : Finset Var)) (((syn_c1st)).fv) from
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
  have dv_cache_0004 : x ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv :=
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
      ((Wff.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
            (syn_chwcn A)))).fv :=
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
    @g_hnwcutcodeeq3 (.cv x) B (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      dv_cache_0001
  have p0001 :=
    @g_eleq1
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
      (syn_chwcn A)
  have p0002 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
      (syn_wb (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
          (syn_chwcn A)))
      p0000 p0001
  have p0003 :=
    @g_imbi2d (.classEq (.cv x) B)
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
        (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A)) p0002
  have p0004 := @g_hnwcutcodeambientndv x u A dv_cache_0002
  have p0005 :=
    @g_expcom (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0004
  have p0006 :=
    @g_vtoclga
      (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)))
      (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
          (syn_chwcn A)))
      x B (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0003
      p0005
  have p0007 :=
    @g_impcom (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
        (syn_chwcn A))
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

@[expose]
noncomputable def g_hnwcutcodepartsclndv (u : Var) (A : Class) (B : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem B (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
            (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn B))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn B)))))) (.classEq (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn B)))))) :=
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
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
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
                  (show Disjoint (({ x } : Finset Var)) (((syn_c1st)).fv) from
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
  have dv_cache_0004 : x ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv :=
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
      ((Wff.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classEq (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
              (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
                  (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                    (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                      (syn_csn B))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                    (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                      (syn_csn B)))))) (.classEq (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn B))))))).fv :=
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
    @g_hnwcutcodeeq3 (.cv x) B (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      dv_cache_0001
  have p0001 :=
    @g_fveq2d (.classEq (.cv x) B)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
      (syn_c1st) p0000
  have p0002 := @g_id (.classEq (.cv x) B)
  have p0003 := @g_sneqd (.classEq (.cv x) B) (.cv x) B p0002
  have p0004 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B)
      (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) p0003
  have p0005 :=
    @g_ineq2
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B))
      (syn_cfv (syn_c2nd) (.cv u))
  have p0006 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x)))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B)))
      (.classEq (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B))))
      p0004 p0005
  have p0012 :=
    @g_xpeq12d (.classEq (.cv x) B)
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B)))
      p0006 p0006
  have p0013 :=
    @g_ineq2
      (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B))))
      (syn_cfv (syn_c1st) (.cv u))
  have p0014 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn B)))))
      (.classEq (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn B))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn B))))))
      p0012 p0013
  have p0015 :=
    @g_eqeq12d (.classEq (.cv x) B)
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn B)))))
      p0001 p0014
  have p0017 :=
    @g_fveq2d (.classEq (.cv x) B)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
      (syn_c2nd) p0000
  have p0023 :=
    @g_eqeq12d (.classEq (.cv x) B)
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B)))
      p0017 p0006
  have p0024 :=
    @g_anbi12d (.classEq (.cv x) B)
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn B))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn B))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn B))))
      p0015 p0023
  have p0025 :=
    @g_imbi2d (.classEq (.cv x) B)
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn B))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn B)))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn B)))))
      (.classMem (.cv u) (syn_chwcn A)) p0024
  have p0026 := @g_hnwcutcodepartsndv x u A dv_cache_0002
  have p0027 :=
    @g_expcom (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0026
  have p0028 :=
    @g_vtoclga
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classEq (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
                (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classEq (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
            (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn B))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn B)))))) (.classEq (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn B))))))
      x B (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0025
      p0027
  have p0029 :=
    @g_impcom (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn B))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn B)))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn B)))))
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

@[expose]
noncomputable def g_hnwcutcodeisoimagendv (x : Var) (v : Var) (u : Var) (A : Class)
    (h : Var) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x))))) :=
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
      ((syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))))).fv :=
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
      ((syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))))).fv :=
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
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
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
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x)))).fv :=
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
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0001 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0000
  have p0003 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0000
  have p0004 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0001 p0003
  have p0005 :=
    @g_isostrictsegresndv x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv h)
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      p0004 p0005
  have p0007 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0008 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0007
  have p0011 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      p0008 p0003
  have p0012 := @g_hnwcutcodepartsndv x u A dv_cache_0001
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0011 p0012
  have p0014 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0013
  have p0015 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0014
  have p0016 :=
    @g_isoeq2
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (syn_cfv (.cv h) (.cv x)))))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wb (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h)
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))))
      p0015 p0016
  have p0019 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0007
  have p0022 :=
    @g_isof1o (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0001
      p0022
  have p0024 := @g_f1of (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv h)
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0023
      p0024
  have p0028 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0025 p0003
  have p0029 :=
    @g_ffvelrn (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x) (.cv h)
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0028 p0029
  have p0031 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0019 p0030
  have p0032 := @g_hnwcutcodepartsclndv v A (syn_cfv (.cv h) (.cv x)) dv_cache_0002
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv h) (.cv x)))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))))
      p0031 p0032
  have p0034 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      p0033
  have p0035 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))))
      p0034
  have p0036 :=
    @g_isoeq3
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (syn_cfv (.cv h) (.cv x)))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))))
      (syn_wb (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h)
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))))
      p0035 p0036
  have p0038 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      p0017 p0037
  have p0046 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0013
  have p0047 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      p0046
  have p0048 :=
    @g_isoeq4
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (syn_cfv (.cv h) (.cv x)))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wb (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h)
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))))
      p0047 p0048
  have p0050 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      p0038 p0049
  have p0067 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      p0033
  have p0068 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (syn_cfv (.cv h) (.cv x)))))
      p0067
  have p0069 :=
    @g_isoeq5
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (syn_cfv (.cv h) (.cv x)))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))))
      (syn_wb (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h)
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x))))))
      p0068 p0069
  have p0071 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))))
      p0050 p0070
  have p0072 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (syn_cfv (.cv h) (.cv x))))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))))
      p0006 p0071
  have p0073 := @g_vex h
  have p0074 :=
    @g_a1i (.classMem (.cv h) (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      p0073
  have p0075 :=
    @g_fvex
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_c2nd)
  have p0076 :=
    @g_a1i
      (.classMem (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      p0075
  have p0085 :=
    @g_eleq1d
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cvv) p0046
  have p0086 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cvv))
      (.classMem (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cvv))
      p0076 p0085
  have p0087 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv h) (syn_cvv))
      (.classMem (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cvv))
      p0074 p0086
  have p0088 :=
    @g_resexg (.cv h)
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cvv) (syn_cvv)
  have p0089 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv h) (syn_cvv)) (.classMem (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cvv)))
      (.classMem (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cvv))
      p0087 p0088
  have p0090 :=
    @g_isoeq1
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      (.cv g)
  have p0091 :=
    @g_spcegv
      (syn_wiso (.cv g) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))))
      g
      (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cvv) dv_cache_0003 dv_cache_0004 p0090
  have p0092 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cvv))
      (.imp (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x))))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (syn_cfv (.cv h) (.cv x)))))))
      p0089 p0091
  have p0093 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x))))))
      p0072 p0092
  have p0099 := @g_hnwcutcodeambientndv x u A dv_cache_0001
  have p0100 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0011 p0099
  have p0115 := @g_hnwcutcodeambientclndv v A (syn_cfv (.cv h) (.cv x)) dv_cache_0002
  have p0116 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))) (syn_chwcn A))
      p0031 p0115
  have p0117 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))) (syn_chwcn A))
      p0100 p0116
  have p0118 :=
    @g_hwnisodirectisobclndv A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
        (syn_cfv (.cv h) (.cv x)))
      g dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0119 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x))) (syn_chwcn A)))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (syn_cfv (.cv h) (.cv x)))))))
      p0117 p0118
  have p0120 :=
    @g_biimprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x))))))
      p0119
  have p0121 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (syn_cfv (.cv h) (.cv x))))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
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

@[expose]
noncomputable def g_hnwcutcodetransportndv (x : Var) (y : Var) (v : Var) (u : Var)
    (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_u_y : u ≠ y) (dv_v_y : v ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
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
  have dv_cache_0006 : Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ y } : Finset Var)) ((((Class.cv v)).fv) ∪ (((syn_c1st)).fv))
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
                  (show Disjoint (({ y } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ y } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0007 : y ∉ ((syn_cfv (.cv h) (.cv x))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv :=
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
      ((syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x))))).fv :=
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
      ((syn_wrex y (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
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
      ((syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0001 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0000
  have p0002 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0003 :=
    @g_hwnisodirectisobclndv A (.cv u) (.cv v) h dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0002 p0003
  have p0005 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0004
  have p0006 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0001 p0005
  have p0009 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0000
  have p0010 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0002 p0009
  have p0011 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
  have p0012 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0011
  have p0013 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
  have p0015 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0011
  have p0016 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0013 p0015
  have p0017 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0012 p0016
  have p0018 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0019 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0018
  have p0020 :=
    @g_isof1o (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0019
      p0020
  have p0022 := @g_f1of (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv h)
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0021
      p0022
  have p0025 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0018
  have p0026 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0023 p0025
  have p0027 :=
    @g_ffvelrn (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x) (.cv h)
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0026 p0027
  have p0029 := @g_hnwcutcodeisoimagendv x v u A h dv_cache_0004 dv_cache_0005
  have p0030 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      p0028 p0029
  have p0031 :=
    @g_hnwcutcodeeq3 (.cv y) (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv v)) dv_cache_0006
  have p0032 :=
    @g_breq2d (.classEq (.cv y) (syn_cfv (.cv h) (.cv x)))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
        (syn_cfv (.cv h) (.cv x)))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A) p0031
  have p0033 :=
    @g_rspcev
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (.cv h) (.cv x))))
      y (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0032
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (syn_cfv (.cv h) (.cv x)))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      p0030 p0033
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      p0017 p0034
  have p0036 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      p0035
  have p0037 :=
    @g_exlimdv
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      h dv_cache_0010 dv_cache_0011 p0036
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.imp (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv y)))))
      p0010 p0037
  have p0039 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      p0006 p0038
  exact p0039

@[expose]
noncomputable def g_hnwcutcodetransporttgtclndv (x : Var) (y : Var) (u : Var) (A : Class)
    (C : Class) (dv_A_u : u ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_C_y : y ∉ C.fv)
    (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wrex y (syn_cfv (syn_c2nd) C) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y))))) :=
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
  have dv_cache_0001 : y ∉ ((syn_cfv (syn_c2nd) (.cv w))).fv := by
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
  have dv_cache_0002 : y ∉ ((syn_cfv (syn_c2nd) C)).fv :=
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
  have dv_cache_0011 : w ∉ ((syn_chwcn A)).fv :=
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
      ((Wff.imp (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
              (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_wrex y (syn_cfv (syn_c2nd) C) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y)))))).fv :=
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
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0001 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0000
  have p0002 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0003 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0001 p0002
  have p0005 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0000
  have p0006 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem C (syn_chwcn A)) p0003 p0005
  have p0007 := @g_biidd (.classEq (.cv w) C) (.classMem (.cv u) (syn_chwcn A))
  have p0008 := @g_id (.classEq (.cv w) C)
  have p0009 := @g_breq2d (.classEq (.cv w) C) (.cv w) C (.cv u) (syn_chwniso A) p0008
  have p0010 :=
    @g_biidd (.classEq (.cv w) C) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0011 :=
    @g_anbi12d (.classEq (.cv w) C) (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
      (syn_wbr (.cv u) (syn_chwniso A) C) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0009 p0010
  have p0012 :=
    @g_anbi12d (.classEq (.cv w) C) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0007 p0011
  have p0014 := @g_fveq2d (.classEq (.cv w) C) (.cv w) C (syn_c2nd) p0008
  have p0016 := @g_fveq2d (.classEq (.cv w) C) (.cv w) C (syn_c1st) p0008
  have p0019 :=
    @g_jca (.classEq (.cv w) C)
      (.classEq (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c1st) C))
      (.classEq (syn_cfv (syn_c2nd) (.cv w)) (syn_cfv (syn_c2nd) C)) p0016 p0014
  have p0020 :=
    @g_hnwcutcodeeq12ndv y (syn_cfv (syn_c2nd) (.cv w)) (syn_cfv (syn_c1st) (.cv w))
      (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C)
  have p0021 :=
    @g_syl (.classEq (.cv w) C)
      (syn_wa (.classEq (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c1st) C))
        (.classEq (syn_cfv (syn_c2nd) (.cv w)) (syn_cfv (syn_c2nd) C)))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
          (.cv y)) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y)))
      p0019 p0020
  have p0022 :=
    @g_breq2d (.classEq (.cv w) C)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A) p0021
  have p0023 :=
    @g_rexeqbidv (.classEq (.cv w) C)
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y)))
      y (syn_cfv (syn_c2nd) (.cv w)) (syn_cfv (syn_c2nd) C) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0014 p0022
  have p0024 :=
    @g_imbi12d (.classEq (.cv w) C)
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
      (syn_wrex y (syn_cfv (syn_c2nd) C) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y))))
      p0012 p0023
  have p0025 :=
    @g_simpr (.classMem (.cv w) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0026 :=
    @g_simpld
      (syn_wa (.classMem (.cv w) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0025
  have p0027 :=
    @g_simpl (.classMem (.cv w) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0028 :=
    @g_jca
      (syn_wa (.classMem (.cv w) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0026 p0027
  have p0030 :=
    @g_simprd
      (syn_wa (.classMem (.cv w) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0025
  have p0031 :=
    @g_jca
      (syn_wa (.classMem (.cv w) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0028 p0030
  have p0032 :=
    @g_hnwcutcodetransportndv x y w u A dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0033 :=
    @g_syl
      (syn_wa (.classMem (.cv w) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
      p0031 p0032
  have p0034 :=
    @g_ex (.classMem (.cv w) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))
      p0033
  have p0035 :=
    @g_vtoclga
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w))
              (.cv y)))))
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wrex y (syn_cfv (syn_c2nd) C) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y)))))
      w C (syn_chwcn A) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0024 p0034
  have p0036 :=
    @g_impcom (.classMem C (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex y (syn_cfv (syn_c2nd) C) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y))))
      p0035
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) C)
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem C (syn_chwcn A)))
      (syn_wrex y (syn_cfv (syn_c2nd) C) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv y))))
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

@[expose]
noncomputable def g_hnwcutcodetransportintocutndv (x : Var) (y : Var) (z : Var) (v : Var)
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_u_z : u ≠ z) (dv_v_z : v ≠ z) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wrex z (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
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
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
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
  have dv_cache_0007 : Disjoint ((Class.cv z)).fv ((syn_cfv (syn_c1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv z)).fv ((syn_cfv (syn_c1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var)) ((((Class.cv v)).fv) ∪ (((syn_c1st)).fv))
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
                  (show Disjoint (({ z } : Finset Var)) (((syn_c1st)).fv) from
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
  have dv_cache_0009 : z ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv :=
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
      ((syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
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
      ((syn_wrex z (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
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
      ((syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
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
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0001 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))) p0000
  have p0002 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0005 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0007 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))) p0000
  have p0008 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))
      p0005 p0007
  have p0009 := @g_hnwcutcodeambientndv y v A dv_cache_0001
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv y)) (syn_chwcn A))
      p0008 p0009
  have p0011 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv y)) (syn_chwcn A))
      p0002 p0010
  have p0012 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0013 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0012
  have p0015 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0012
  have p0016 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0013 p0015
  have p0017 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))
          (syn_chwcn A)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0011 p0016
  have p0018 :=
    @g_hnwcutcodetransporttgtclndv x w u A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))
            (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex w (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.cv w))))
      p0017 p0018
  have p0020 :=
    @g_simpr
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv w) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv y)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.cv w))))
  have p0021 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)))
      p0020
  have p0022 :=
    @g_simpl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv w) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv y)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.cv w))))
  have p0029 := @g_hnwcutcodepartsndv y v A dv_cache_0001
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))))
      p0008 p0029
  have p0031 :=
    @g_simprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0022 p0031
  have p0033 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv y))))
      (.cv w) p0032
  have p0034 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      (.classMem (.cv w) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0021 p0033
  have p0035 :=
    @g_inss1 (syn_cfv (syn_c2nd) (.cv v))
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv y)))
  have p0036 :=
    @g_sseli
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv y))))
      (syn_cfv (syn_c2nd) (.cv v)) (.cv w) p0035
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      (.classMem (.cv w) (syn_cfv (syn_c2nd) (.cv v))) p0034 p0036
  have p0039 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)))
      p0020
  have p0049 :=
    @g_simpld
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0030
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))))
      p0022 p0049
  have p0062 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0050 p0032
  have p0063 :=
    @g_hnwcutcodeeq12ndv w
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv y))))
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)) (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y)))) (.cv w)))
      p0062 p0063
  have p0069 := @g_hwcnweclndv A (.cv v)
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v))) p0005
      p0069
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v))) p0022
      p0070
  have p0075 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))) p0022 p0007
  have p0076 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))) p0071 p0075
  have p0092 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv w) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0076 p0034
  have p0093 :=
    @g_hnwcutcodenestndv w y (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v))
  have p0094 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (syn_wa
          (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (.cv w)
          (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y))))))
      (.classEq (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv y)))) (.cv w))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w)))
      p0092 p0093
  have p0095 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.cv w))
      (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv y)))) (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w))
      p0064 p0094
  have p0096 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
        (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A) p0095
  have p0097 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w)))
      p0039 p0096
  have p0098 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w)))
      p0037 p0097
  have p0099 :=
    @g_hnwcutcodeeq3 (.cv z) (.cv w) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv v)) dv_cache_0007
  have p0100 :=
    @g_breq2d (.classEq (.cv z) (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A) p0099
  have p0101 :=
    @g_rspcev
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w)))
      z (.cv w) (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0008 dv_cache_0009 dv_cache_0010
      p0100
  have p0102 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa
          (.classMem (.cv w) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv y)))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (syn_wa (.classMem (.cv w) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv w))))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      p0098 p0101
  have p0103 :=
    @g_rexlimddv
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
          (.cv w)))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      w
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv y)))
      dv_cache_0011 dv_cache_0012 p0019 p0102
  exact p0103


end NFChoice.DirectNominalPrf.WPPReplay

end
