/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk005

/-! NF weak partition development: NominalWPPReplayChunk006. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nfcrd (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) (hyp_nfeqd_1 : Nominal.NPrf (.imp ph (syn_wnfc x A))) :
    Nominal.NPrf (.imp ph (syn_wnf x (.classMem (.cv y) A))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcr x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_syl ph (syn_wnfc x A) (syn_wnf x (.classMem (.cv y) A)) hyp_nfeqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_nfeqd (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfeqd_1 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_nfeqd_2 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wnf x (.classEq A B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_dfcleq y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfcrd ph x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_nfeqd_1
  have p0003 :=
    @g_nfcrd ph x y B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_nfeqd_2
  have p0004 := @g_nfbid ph (.classMem (.cv y) A) (.classMem (.cv y) B) x p0002 p0003
  have p0005 :=
    @g_nfald ph (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)) x y p0001 p0004
  have p0006 :=
    @g_nfxfrd (.classEq A B) (.all y (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)))
      ph x p0000 p0005
  exact p0006

@[expose]
noncomputable def g_nfeld (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfeqd_1 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_nfeqd_2 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wnf x (.classMem A B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y A B (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0001 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfcvd ph x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 := @g_nfeqd ph x (.cv y) A p0002 hyp_nfeqd_1
  have p0004 :=
    @g_nfcrd ph x y B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_nfeqd_2
  have p0005 := @g_nfand ph (.classEq (.cv y) A) (.classMem (.cv y) B) x p0003 p0004
  have p0006 :=
    @g_nfexd ph (syn_wa (.classEq (.cv y) A) (.classMem (.cv y) B)) x y p0001 p0005
  have p0007 :=
    @g_nfxfrd (.classMem A B)
      (syn_wex y (syn_wa (.classEq (.cv y) A) (.classMem (.cv y) B))) ph x p0000 p0006
  exact p0007

@[expose]
noncomputable def g_drnfc1 (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_drnfc1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (.classEq A B))) :
    Nominal.NPrf
      (.imp (.all x (.classEq (.cv x) (.cv y))) (syn_wb (syn_wnfc x A) (syn_wnfc y B))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have p0000_e00_recanon :
    Nominal.NPrf (.imp (.all x (.classEq (.cv x) (.cv y))) (.classEq A B)) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_drnfc1_1
  have p0000 :=
    @g_eleq2d (.all x (.classEq (.cv x) (.cv y))) A B (.cv w) p0000_e00_recanon
  have p0001_e00_recanon :
    Nominal.NPrf
      (.imp (.all x (.objEq x y)) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0001 := @g_drnf1 (.classMem (.cv w) A) (.classMem (.cv w) B) x y p0001_e00_recanon
  have p0002 :=
    @g_dral2 (syn_wnf x (.classMem (.cv w) A)) (syn_wnf y (.classMem (.cv w) B)) x y w
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x w A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc y w B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.all x (.classEq (.cv x) (.cv y)))
        (syn_wb (.all w (syn_wnf x (.classMem (.cv w) A)))
          (.all w (syn_wnf y (.classMem (.cv w) B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0005 :=
    @g_n_3bitr4g (.all x (.classEq (.cv x) (.cv y)))
      (.all w (syn_wnf x (.classMem (.cv w) A)))
      (.all w (syn_wnf y (.classMem (.cv w) B))) (syn_wnfc x A) (syn_wnfc y B)
      p0005_e00_recanon p0003 p0004
  exact p0005

@[expose]
noncomputable def g_nfabd2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfabd2_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfabd2_2 :
      Nominal.NPrf (.imp (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnfc x (.cab y ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 :=
    @g_nfv (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      z y ps)
  have p0002 := @g_nfnae x y y
  have p0003_e01_recanon :
    Nominal.NPrf (syn_wnf y (.neg (.all x (.classEq (.cv x) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wnf
        apply Nominal.RecanonTransportDev.TRecanonWff.all
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0002
  have p0003 :=
    @g_nfan ph (.neg (.all x (.classEq (.cv x) (.cv y)))) y hyp_nfabd2_1 p0003_e01_recanon
  have p0004_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) (syn_wnf x ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_nfabd2_2
  have p0004 :=
    @g_nfsbd (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) ps y z x
      (by
        first
        | (aesop))
      p0003 p0004_e01_recanon
  have p0005 :=
    @g_nfxfrd (.classMem (.cv z) (.cab y ps)) (syn_wsb z y ps)
      (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) x p0001 p0004
  have p0006 :=
    @g_nfcd (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) x z (.cab y ps)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0000 p0005
  have p0007 :=
    @g_ex ph (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnfc x (.cab y ps)) p0006
  have p0008 := @g_nfab1 ps y
  have p0009 := @g_eqidd (.all x (.classEq (.cv x) (.cv y))) (.cab y ps)
  have p0010_e00_recanon :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.classEq (.cab y ps) (.cab y ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 := @g_drnfc1 x y (.cab y ps) (.cab y ps) p0010_e00_recanon
  have p0011 :=
    @g_mpbiri (.all x (.classEq (.cv x) (.cv y))) (syn_wnfc x (.cab y ps))
      (syn_wnfc y (.cab y ps)) p0008 p0010
  have p0012 :=
    @g_pm2_61d2 ph (.all x (.classEq (.cv x) (.cv y))) (syn_wnfc x (.cab y ps)) p0007
      p0011
  exact p0012

@[expose]
noncomputable def g_nfabd (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfabd_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfabd_2 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnfc x (.cab y ps))) :=
  by
  have p0000 :=
    @g_adantr ph (syn_wnf x ps) (.neg (.all x (.classEq (.cv x) (.cv y)))) hyp_nfabd_2
  have p0001_e01_recanon :
    Nominal.NPrf (.imp (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wnf x ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0001 := @g_nfabd2 ph ps x y hyp_nfabd_1 p0001_e01_recanon
  exact p0001

@[expose]
noncomputable def g_dvelimdc (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (hyp_dvelimdc_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_dvelimdc_2 : Nominal.NPrf (syn_wnf z ph))
    (hyp_dvelimdc_3 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_dvelimdc_4 : Nominal.NPrf (.imp ph (syn_wnfc z B)))
    (hyp_dvelimdc_5 : Nominal.NPrf (.imp ph (.imp (.objEq z y) (.classEq A B)))) :
    Nominal.NPrf
      (.imp ph (.imp (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnfc x B))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪
      B.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_nfv (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 :=
    @g_nfcrd ph x w A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_dvelimdc_3
  have p0002 :=
    @g_nfcrd ph z w B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_dvelimdc_4
  have p0003 := @g_eleq2 A B (.cv w)
  have p0004_e00_recanon :
    Nominal.NPrf (.imp ph (.imp (.classEq (.cv z) (.cv y)) (.classEq A B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_dvelimdc_5
  have p0004 :=
    @g_syl6 ph (.classEq (.cv z) (.cv y)) (.classEq A B)
      (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)) p0004_e00_recanon p0003
  have p0005_e04_recanon :
    Nominal.NPrf
      (.imp ph (.imp (.objEq z y) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_dvelimdf ph (.classMem (.cv w) A) (.classMem (.cv w) B) x y z hyp_dvelimdc_1
      hyp_dvelimdc_2 p0001 p0002 p0005_e04_recanon
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp ph (.imp (.neg (.all x (.classEq (.cv x) (.cv y))))
          (syn_wnf x (.classMem (.cv w) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_imp ph (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnf x (.classMem (.cv w) B))
      p0006_e00_recanon
  have p0007 :=
    @g_nfcd (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) x w B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0006
  have p0008 := @g_ex ph (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnfc x B) p0007
  exact p0008

@[expose]
noncomputable def g_dvelimc (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (hyp_dvelimc_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_dvelimc_2 : Nominal.NPrf (syn_wnfc z B))
    (hyp_dvelimc_3 : Nominal.NPrf (.imp (.objEq z y) (.classEq A B))) :
    Nominal.NPrf (.imp (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnfc x B)) :=
  by
  have p0000 := @g_nftru x
  have p0001 := @g_nftru z
  have p0002 := @g_a1i (syn_wnfc x A) syn_wtru hyp_dvelimc_1
  have p0003 := @g_a1i (syn_wnfc z B) syn_wtru hyp_dvelimc_2
  have p0004_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv z) (.cv y)) (.classEq A B)) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_dvelimc_3
  have p0004 :=
    @g_a1i (.imp (.classEq (.cv z) (.cv y)) (.classEq A B)) syn_wtru p0004_e00_recanon
  have p0005_e04_recanon :
    Nominal.NPrf (.imp syn_wtru (.imp (.objEq z y) (.classEq A B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wtru
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 := @g_dvelimdc syn_wtru x y z A B p0000 p0001 p0002 p0003 p0005_e04_recanon
  have p0006 :=
    @g_trud (.imp (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnfc x B)) p0005
  exact p0006

@[expose]
noncomputable def g_nfcvf (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnfc x (.cv y))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 :=
    @g_nfcv x (.cv z)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 :=
    @g_nfcv z (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @g_id (.classEq (.cv z) (.cv y))
  have p0003_e02_recanon : Nominal.NPrf (.imp (.objEq z y) (.classEq (.cv z) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 := @g_dvelimc x y z (.cv z) (.cv y) p0000 p0001 p0003_e02_recanon
  exact p0003

@[expose]
noncomputable def g_cleqf (x : Var) (A : Class) (B : Class)
    (hyp_cleqf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_cleqf_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_dfcleq y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 :=
    @g_nfcri x y A
      (by
        first
        | (aesop))
      hyp_cleqf_1
  have p0003 :=
    @g_nfcri x y B
      (by
        first
        | (aesop))
      hyp_cleqf_2
  have p0004 := @g_nfbi (.classMem (.cv y) A) (.classMem (.cv y) B) x p0002 p0003
  have p0005 := @g_eleq1 (.cv x) (.cv y) A
  have p0006 := @g_eleq1 (.cv x) (.cv y) B
  have p0007 :=
    @g_bibi12d (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0005 p0006
  have p0008_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
          (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_cbval (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)) x y p0001 p0004
      p0008_e02_recanon
  have p0009 :=
    @g_bitr4i (.classEq A B) (.all y (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)))
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_nne (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.neg (syn_wne A B)) (.classEq A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wne A B))
  have p0001 := @g_con2bii (syn_wne A B) (.classEq A B) p0000
  have p0002 := @g_bicomi (.classEq A B) (.neg (syn_wne A B)) p0001
  exact p0002

@[expose]
noncomputable def g_neirr (A : Class) : Nominal.NPrf (.neg (syn_wne A A)) :=
  by
  have p0000 := @g_eqid A
  have p0001 := @g_nne A A
  have p0002 := @g_mpbir (.neg (syn_wne A A)) (.classEq A A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_neeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wne A C) (syn_wne B C))) :=
  by
  have p0000 := @g_eqeq1 A B C
  have p0001 := @g_notbid (.classEq A B) (.classEq A C) (.classEq B C) p0000
  have p0002 := (Nominal.biimpRefl (syn_wne A C))
  have p0003 := (Nominal.biimpRefl (syn_wne B C))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (.neg (.classEq A C)) (.neg (.classEq B C)) (syn_wne A C)
      (syn_wne B C) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_neeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wne C A) (syn_wne C B))) :=
  by
  have p0000 := @g_eqeq2 A B C
  have p0001 := @g_notbid (.classEq A B) (.classEq C A) (.classEq C B) p0000
  have p0002 := (Nominal.biimpRefl (syn_wne C A))
  have p0003 := (Nominal.biimpRefl (syn_wne C B))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (.neg (.classEq C A)) (.neg (.classEq C B)) (syn_wne C A)
      (syn_wne C B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_neeq1i (A : Class) (B : Class) (C : Class)
    (hyp_neeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wne A C) (syn_wne B C)) :=
  by
  have p0000 := @g_neeq1 A B C
  have p0001 := Nominal.mp hyp_neeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_neeq2i (A : Class) (B : Class) (C : Class)
    (hyp_neeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wne C A) (syn_wne C B)) :=
  by
  have p0000 := @g_neeq2 A B C
  have p0001 := Nominal.mp hyp_neeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_neeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_neeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wne A C) (syn_wne B C))) :=
  by
  have p0000 := @g_neeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wne A C) (syn_wne B C)) hyp_neeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_neeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_neeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wne C A) (syn_wne C B))) :=
  by
  have p0000 := @g_neeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wne C A) (syn_wne C B)) hyp_neeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_neeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_neeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_neeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wne A C) (syn_wne B D))) :=
  by
  have p0000 := @g_neeq1d ph A B C hyp_neeq1d_1
  have p0001 := @g_neeq2d ph C D B hyp_neeq12d_2
  have p0002 := @g_bitrd ph (syn_wne A C) (syn_wne B C) (syn_wne B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_neneqd (ph : Wff) (A : Class) (B : Class)
    (hyp_neneqd_1 : Nominal.NPrf (.imp ph (syn_wne A B))) :
    Nominal.NPrf (.imp ph (.neg (.classEq A B))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wne A B))
  have p0001 := @g_sylib ph (syn_wne A B) (.neg (.classEq A B)) hyp_neneqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqnetri (A : Class) (B : Class) (C : Class)
    (hyp_eqnetr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqnetr_2 : Nominal.NPrf (syn_wne B C)) : Nominal.NPrf (syn_wne A C) :=
  by
  have p0000 := @g_neeq1i A B C hyp_eqnetr_1
  have p0001 := @g_mpbir (syn_wne A C) (syn_wne B C) hyp_eqnetr_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqnetrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqnetrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqnetrd_2 : Nominal.NPrf (.imp ph (syn_wne B C))) :
    Nominal.NPrf (.imp ph (syn_wne A C)) :=
  by
  have p0000 := @g_neeq1d ph A B C hyp_eqnetrd_1
  have p0001 := @g_mpbird ph (syn_wne A C) (syn_wne B C) hyp_eqnetrd_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqnetrri (A : Class) (B : Class) (C : Class)
    (hyp_eqnetrr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqnetrr_2 : Nominal.NPrf (syn_wne A C)) : Nominal.NPrf (syn_wne B C) :=
  by
  have p0000 := @g_eqcomi A B hyp_eqnetrr_1
  have p0001 := @g_eqnetri B A C p0000 hyp_eqnetrr_2
  exact p0001

@[expose]
noncomputable def g_eqnetrrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqnetrrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqnetrrd_2 : Nominal.NPrf (.imp ph (syn_wne A C))) :
    Nominal.NPrf (.imp ph (syn_wne B C)) :=
  by
  have p0000 := @g_eqcomd ph A B hyp_eqnetrrd_1
  have p0001 := @g_eqnetrd ph B A C p0000 hyp_eqnetrrd_2
  exact p0001

@[expose]
noncomputable def g_necon3abii (ph : Wff) (A : Class) (B : Class)
    (hyp_necon3abii_1 : Nominal.NPrf (syn_wb (.classEq A B) ph)) :
    Nominal.NPrf (syn_wb (syn_wne A B) (.neg ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wne A B))
  have p0001 := @g_xchbinx (syn_wne A B) (.classEq A B) ph p0000 hyp_necon3abii_1
  exact p0001

@[expose]
noncomputable def g_necon3bbii (ph : Wff) (A : Class) (B : Class)
    (hyp_necon3bbii_1 : Nominal.NPrf (syn_wb ph (.classEq A B))) :
    Nominal.NPrf (syn_wb (.neg ph) (syn_wne A B)) :=
  by
  have p0000 := @g_bicomi ph (.classEq A B) hyp_necon3bbii_1
  have p0001 := @g_necon3abii ph A B p0000
  have p0002 := @g_bicomi (syn_wne A B) (.neg ph) p0001
  exact p0002

@[expose]
noncomputable def g_necon3bii (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon3bii_1 : Nominal.NPrf (syn_wb (.classEq A B) (.classEq C D))) :
    Nominal.NPrf (syn_wb (syn_wne A B) (syn_wne C D)) :=
  by
  have p0000 := @g_necon3abii (.classEq C D) A B hyp_necon3bii_1
  have p0001 := (Nominal.biimpRefl (syn_wne C D))
  have p0002 := @g_bitr4i (syn_wne A B) (.neg (.classEq C D)) (syn_wne C D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_necon3abid (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon3abid_1 : Nominal.NPrf (.imp ph (syn_wb (.classEq A B) ps))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wne A B) (.neg ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wne A B))
  have p0001 := @g_notbid ph (.classEq A B) ps hyp_necon3abid_1
  have p0002 := @g_syl5bb (syn_wne A B) (.neg (.classEq A B)) ph (.neg ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_necon3bbid (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon3bbid_1 : Nominal.NPrf (.imp ph (syn_wb ps (.classEq A B)))) :
    Nominal.NPrf (.imp ph (syn_wb (.neg ps) (syn_wne A B))) :=
  by
  have p0000 := @g_bicomd ph ps (.classEq A B) hyp_necon3bbid_1
  have p0001 := @g_necon3abid ph ps A B p0000
  have p0002 := @g_bicomd ph (syn_wne A B) (.neg ps) p0001
  exact p0002

@[expose]
noncomputable def g_necon3ad (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon3ad_1 : Nominal.NPrf (.imp ph (.imp ps (.classEq A B)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wne A B) (.neg ps))) :=
  by
  have p0000 := @g_nne A B
  have p0001 := @g_syl6ibr ph ps (.classEq A B) (.neg (syn_wne A B)) hyp_necon3ad_1 p0000
  have p0002 := @g_con2d ph ps (syn_wne A B) p0001
  exact p0002

@[expose]
noncomputable def g_necon3bd (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon3bd_1 : Nominal.NPrf (.imp ph (.imp (.classEq A B) ps))) :
    Nominal.NPrf (.imp ph (.imp (.neg ps) (syn_wne A B))) :=
  by
  have p0000 := @g_nne A B
  have p0001 := @g_syl5bi (.neg (syn_wne A B)) (.classEq A B) ph ps p0000 hyp_necon3bd_1
  have p0002 := @g_con1d ph (syn_wne A B) ps p0001
  exact p0002

@[expose]
noncomputable def g_necon3d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon3d_1 : Nominal.NPrf (.imp ph (.imp (.classEq A B) (.classEq C D)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wne C D) (syn_wne A B))) :=
  by
  have p0000 := @g_necon3ad ph (.classEq A B) C D hyp_necon3d_1
  have p0001 := (Nominal.biimpRefl (syn_wne A B))
  have p0002 :=
    @g_syl6ibr ph (syn_wne C D) (.neg (.classEq A B)) (syn_wne A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_necon3i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon3i_1 : Nominal.NPrf (.imp (.classEq A B) (.classEq C D))) :
    Nominal.NPrf (.imp (syn_wne C D) (syn_wne A B)) :=
  by
  have p0000 := @g_id (.imp (.classEq A B) (.classEq C D))
  have p0001 := @g_necon3d (.imp (.classEq A B) (.classEq C D)) A B C D p0000
  have p0002 := Nominal.mp hyp_necon3i_1 p0001
  exact p0002

@[expose]
noncomputable def g_necon3ai (ph : Wff) (A : Class) (B : Class)
    (hyp_necon3ai_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp (syn_wne A B) (.neg ph)) :=
  by
  have p0000 := @g_nne A B
  have p0001 := @g_sylibr ph (.classEq A B) (.neg (syn_wne A B)) hyp_necon3ai_1 p0000
  have p0002 := @g_con2i ph (syn_wne A B) p0001
  exact p0002

@[expose]
noncomputable def g_necon3bi (ph : Wff) (A : Class) (B : Class)
    (hyp_necon3bi_1 : Nominal.NPrf (.imp (.classEq A B) ph)) :
    Nominal.NPrf (.imp (.neg ph) (syn_wne A B)) :=
  by
  have p0000 := @g_nne A B
  have p0001 := @g_sylbi (.neg (syn_wne A B)) (.classEq A B) ph p0000 hyp_necon3bi_1
  have p0002 := @g_con1i (syn_wne A B) ph p0001
  exact p0002

@[expose]
noncomputable def g_necon1ai (ph : Wff) (A : Class) (B : Class)
    (hyp_necon1ai_1 : Nominal.NPrf (.imp (.neg ph) (.classEq A B))) :
    Nominal.NPrf (.imp (syn_wne A B) ph) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wne A B))
  have p0001 := @g_con1i ph (.classEq A B) hyp_necon1ai_1
  have p0002 := @g_sylbi (syn_wne A B) (.neg (.classEq A B)) ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_necon1bi (ph : Wff) (A : Class) (B : Class)
    (hyp_necon1bi_1 : Nominal.NPrf (.imp (syn_wne A B) ph)) :
    Nominal.NPrf (.imp (.neg ph) (.classEq A B)) :=
  by
  have p0000 := @g_con3i (syn_wne A B) ph hyp_necon1bi_1
  have p0001 := @g_nne A B
  have p0002 := @g_sylib (.neg ph) (.neg (syn_wne A B)) (.classEq A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_necon2ai (ph : Wff) (A : Class) (B : Class)
    (hyp_necon2ai_1 : Nominal.NPrf (.imp (.classEq A B) (.neg ph))) :
    Nominal.NPrf (.imp ph (syn_wne A B)) :=
  by
  have p0000 := @g_nne A B
  have p0001 :=
    @g_sylbi (.neg (syn_wne A B)) (.classEq A B) (.neg ph) p0000 hyp_necon2ai_1
  have p0002 := @g_con4i (syn_wne A B) ph p0001
  exact p0002

@[expose]
noncomputable def g_necon2bi (ph : Wff) (A : Class) (B : Class)
    (hyp_necon2bi_1 : Nominal.NPrf (.imp ph (syn_wne A B))) :
    Nominal.NPrf (.imp (.classEq A B) (.neg ph)) :=
  by
  have p0000 := @g_neneqd ph A B hyp_necon2bi_1
  have p0001 := @g_con2i ph (.classEq A B) p0000
  exact p0001

@[expose]
noncomputable def g_necon2ad (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon2ad_1 : Nominal.NPrf (.imp ph (.imp (.classEq A B) (.neg ps)))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wne A B))) :=
  by
  have p0000 := @g_nne A B
  have p0001 :=
    @g_syl5bi (.neg (syn_wne A B)) (.classEq A B) ph (.neg ps) p0000 hyp_necon2ad_1
  have p0002 := @g_con4d ph (syn_wne A B) ps p0001
  exact p0002

@[expose]
noncomputable def g_necon2bd (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon2bd_1 : Nominal.NPrf (.imp ph (.imp ps (syn_wne A B)))) :
    Nominal.NPrf (.imp ph (.imp (.classEq A B) (.neg ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wne A B))
  have p0001 := @g_syl6ib ph ps (syn_wne A B) (.neg (.classEq A B)) hyp_necon2bd_1 p0000
  have p0002 := @g_con2d ph ps (.classEq A B) p0001
  exact p0002

@[expose]
noncomputable def g_necon1bbii (ph : Wff) (A : Class) (B : Class)
    (hyp_necon1bbii_1 : Nominal.NPrf (syn_wb (syn_wne A B) ph)) :
    Nominal.NPrf (syn_wb (.neg ph) (.classEq A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wne A B))
  have p0001 := @g_bitr3i (.neg (.classEq A B)) (syn_wne A B) ph p0000 hyp_necon1bbii_1
  have p0002 := @g_con1bii (.classEq A B) ph p0001
  exact p0002

@[expose]
noncomputable def g_necon2bbii (ph : Wff) (A : Class) (B : Class)
    (hyp_necon2bbii_1 : Nominal.NPrf (syn_wb ph (syn_wne A B))) :
    Nominal.NPrf (syn_wb (.classEq A B) (.neg ph)) :=
  by
  have p0000 := @g_bicomi ph (syn_wne A B) hyp_necon2bbii_1
  have p0001 := @g_necon1bbii ph A B p0000
  have p0002 := @g_bicomi (.neg ph) (.classEq A B) p0001
  exact p0002

@[expose]
noncomputable def g_necon4i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon4i_1 : Nominal.NPrf (.imp (syn_wne A B) (syn_wne C D))) :
    Nominal.NPrf (.imp (.classEq C D) (.classEq A B)) :=
  by
  have p0000 := @g_necon2bi (syn_wne A B) C D hyp_necon4i_1
  have p0001 := @g_nne A B
  have p0002 := @g_sylib (.classEq C D) (.neg (syn_wne A B)) (.classEq A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_necon4d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon4d_1 : Nominal.NPrf (.imp ph (.imp (syn_wne A B) (syn_wne C D)))) :
    Nominal.NPrf (.imp ph (.imp (.classEq C D) (.classEq A B))) :=
  by
  have p0000 := @g_necon2bd ph (syn_wne A B) C D hyp_necon4d_1
  have p0001 := @g_nne A B
  have p0002 :=
    @g_syl6ib ph (.classEq C D) (.neg (syn_wne A B)) (.classEq A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm2_21ddne (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_pm2_21ddne_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_pm2_21ddne_2 : Nominal.NPrf (.imp ph (syn_wne A B))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_neneqd ph A B hyp_pm2_21ddne_2
  have p0001 := @g_pm2_21dd ph (.classEq A B) ps hyp_pm2_21ddne_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm2_61ine (ph : Wff) (A : Class) (B : Class)
    (hyp_pm2_61ine_1 : Nominal.NPrf (.imp (.classEq A B) ph))
    (hyp_pm2_61ine_2 : Nominal.NPrf (.imp (syn_wne A B) ph)) : Nominal.NPrf ph :=
  by
  have p0000 := @g_nne A B
  have p0001 := @g_sylbi (.neg (syn_wne A B)) (.classEq A B) ph p0000 hyp_pm2_61ine_1
  have p0002 := @g_pm2_61i (syn_wne A B) ph hyp_pm2_61ine_2 p0001
  exact p0002

@[expose]
noncomputable def g_pm2_61dne (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_pm2_61dne_1 : Nominal.NPrf (.imp ph (.imp (.classEq A B) ps)))
    (hyp_pm2_61dne_2 : Nominal.NPrf (.imp ph (.imp (syn_wne A B) ps))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_nne A B
  have p0001 := @g_syl5bi (.neg (syn_wne A B)) (.classEq A B) ph ps p0000 hyp_pm2_61dne_1
  have p0002 := @g_pm2_61d ph (syn_wne A B) ps hyp_pm2_61dne_2 p0001
  exact p0002

@[expose]
noncomputable def g_necom (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wne A B) (syn_wne B A)) :=
  by
  have p0000 := @g_eqcom A B
  have p0001 := @g_necon3bii A B B A p0000
  exact p0001

@[expose]
noncomputable def g_necomi (A : Class) (B : Class)
    (hyp_necomi_1 : Nominal.NPrf (syn_wne A B)) : Nominal.NPrf (syn_wne B A) :=
  by
  have p0000 := @g_necom A B
  have p0001 := @g_mpbi (syn_wne A B) (syn_wne B A) hyp_necomi_1 p0000
  exact p0001

@[expose]
noncomputable def g_necomd (ph : Wff) (A : Class) (B : Class)
    (hyp_necomd_1 : Nominal.NPrf (.imp ph (syn_wne A B))) :
    Nominal.NPrf (.imp ph (syn_wne B A)) :=
  by
  have p0000 := @g_necom A B
  have p0001 := @g_sylib ph (syn_wne A B) (syn_wne B A) hyp_necomd_1 p0000
  exact p0001

@[expose]
noncomputable def g_nelne2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.neg (.classMem B C))) (syn_wne A B)) :=
  by
  have p0000 := @g_eleq1 A B C
  have p0001 := @g_biimpcd (.classEq A B) (.classMem A C) (.classMem B C) p0000
  have p0002 := @g_necon3bd (.classMem A C) (.classMem B C) A B p0001
  have p0003 := @g_imp (.classMem A C) (.neg (.classMem B C)) (syn_wne A B) p0002
  exact p0003

@[expose]
noncomputable def g_ralnex (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (syn_wb (syn_wral x A (.neg ph)) (.neg (syn_wrex x A ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wral x A (.neg ph)))
  have p0001 := @g_alinexa (.classMem (.cv x) A) ph x
  have p0002 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0003 :=
    @g_xchbinxr (.all x (.imp (.classMem (.cv x) A) (.neg ph)))
      (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) (syn_wrex x A ph) p0001 p0002
  have p0004 :=
    @g_bitri (syn_wral x A (.neg ph)) (.all x (.imp (.classMem (.cv x) A) (.neg ph)))
      (.neg (syn_wrex x A ph)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_rexnal (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (syn_wb (syn_wrex x A (.neg ph)) (.neg (syn_wral x A ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wrex x A (.neg ph)))
  have p0001 := @g_exanali (.classMem (.cv x) A) ph x
  have p0002 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0003 :=
    @g_xchbinxr (syn_wex x (syn_wa (.classMem (.cv x) A) (.neg ph)))
      (.all x (.imp (.classMem (.cv x) A) ph)) (syn_wral x A ph) p0001 p0002
  have p0004 :=
    @g_bitri (syn_wrex x A (.neg ph)) (syn_wex x (syn_wa (.classMem (.cv x) A) (.neg ph)))
      (.neg (syn_wral x A ph)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_dfral2 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (syn_wb (syn_wral x A ph) (.neg (syn_wrex x A (.neg ph)))) :=
  by
  have p0000 := @g_rexnal ph x A
  have p0001 := @g_con2bii (syn_wrex x A (.neg ph)) (syn_wral x A ph) p0000
  exact p0001

@[expose]
noncomputable def g_dfrex2 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (.neg (syn_wral x A (.neg ph)))) :=
  by
  have p0000 := @g_ralnex ph x A
  have p0001 := @g_con2bii (syn_wral x A (.neg ph)) (syn_wrex x A ph) p0000
  exact p0001

@[expose]
noncomputable def g_ralbida (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralbida_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_ralbida_2 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wral x A ps) (syn_wral x A ch))) :=
  by
  have p0000 := @g_pm5_74da ph (.classMem (.cv x) A) ps ch hyp_ralbida_2
  have p0001 :=
    @g_albid ph (.imp (.classMem (.cv x) A) ps) (.imp (.classMem (.cv x) A) ch) x
      hyp_ralbida_1 p0000
  have p0002 := (Nominal.biimpRefl (syn_wral x A ps))
  have p0003 := (Nominal.biimpRefl (syn_wral x A ch))
  have p0004 :=
    @g_n_3bitr4g ph (.all x (.imp (.classMem (.cv x) A) ps))
      (.all x (.imp (.classMem (.cv x) A) ch)) (syn_wral x A ps) (syn_wral x A ch) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_rexbida (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralbida_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_ralbida_2 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wrex x A ps) (syn_wrex x A ch))) :=
  by
  have p0000 := @g_pm5_32da ph (.classMem (.cv x) A) ps ch hyp_ralbida_2
  have p0001 :=
    @g_exbid ph (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv x) A) ch) x
      hyp_ralbida_1 p0000
  have p0002 := (Nominal.biimpRefl (syn_wrex x A ps))
  have p0003 := (Nominal.biimpRefl (syn_wrex x A ch))
  have p0004 :=
    @g_n_3bitr4g ph (syn_wex x (syn_wa (.classMem (.cv x) A) ps))
      (syn_wex x (syn_wa (.classMem (.cv x) A) ch)) (syn_wrex x A ps) (syn_wrex x A ch)
      p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_ralbidva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralbidva_1 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wral x A ps) (syn_wral x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_ralbida ph ps ch x A p0000 hyp_ralbidva_1
  exact p0001

@[expose]
noncomputable def g_rexbidva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralbidva_1 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wrex x A ps) (syn_wrex x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_rexbida ph ps ch x A p0000 hyp_ralbidva_1
  exact p0001

@[expose]
noncomputable def g_ralbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralbid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_ralbid_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wral x A ps) (syn_wral x A ch))) :=
  by
  have p0000 := @g_adantr ph (syn_wb ps ch) (.classMem (.cv x) A) hyp_ralbid_2
  have p0001 := @g_ralbida ph ps ch x A hyp_ralbid_1 p0000
  exact p0001

@[expose]
noncomputable def g_rexbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralbid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_ralbid_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wrex x A ps) (syn_wrex x A ch))) :=
  by
  have p0000 := @g_adantr ph (syn_wb ps ch) (.classMem (.cv x) A) hyp_ralbid_2
  have p0001 := @g_rexbida ph ps ch x A hyp_ralbid_1 p0000
  exact p0001

@[expose]
noncomputable def g_ralbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wral x A ps) (syn_wral x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_ralbid ph ps ch x A p0000 hyp_ralbidv_1
  exact p0001

@[expose]
noncomputable def g_rexbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wrex x A ps) (syn_wrex x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_rexbid ph ps ch x A p0000 hyp_ralbidv_1
  exact p0001

@[expose]
noncomputable def g_rexbidv2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexbidv2_1 : Nominal.NPrf (.imp ph
          (syn_wb (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv x) B) ch)))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wrex x A ps) (syn_wrex x B ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_exbidv ph (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv x) B) ch) x
      (by
        first
        | (aesop))
      hyp_rexbidv2_1
  have p0001 := (Nominal.biimpRefl (syn_wrex x A ps))
  have p0002 := (Nominal.biimpRefl (syn_wrex x B ch))
  have p0003 :=
    @g_n_3bitr4g ph (syn_wex x (syn_wa (.classMem (.cv x) A) ps))
      (syn_wex x (syn_wa (.classMem (.cv x) B) ch)) (syn_wrex x A ps) (syn_wrex x B ch)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ralbii (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wral x A ph) (syn_wral x A ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_a1i (syn_wb ph ps) syn_wtru hyp_ralbii_1
  have p0001 :=
    @g_ralbidv syn_wtru ph ps x A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @g_trud (syn_wb (syn_wral x A ph) (syn_wral x A ps)) p0001
  exact p0002

@[expose]
noncomputable def g_rexbii (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (syn_wrex x A ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_a1i (syn_wb ph ps) syn_wtru hyp_ralbii_1
  have p0001 :=
    @g_rexbidv syn_wtru ph ps x A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @g_trud (syn_wb (syn_wrex x A ph) (syn_wrex x A ps)) p0001
  exact p0002

@[expose]
noncomputable def g_n_2ralbii (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (hyp_ralbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B ph)) (syn_wral x A (syn_wral y B ps))) :=
  by
  have p0000 := @g_ralbii ph ps y B hyp_ralbii_1
  have p0001 := @g_ralbii (syn_wral y B ph) (syn_wral y B ps) x A p0000
  exact p0001

@[expose]
noncomputable def g_n_2rexbii (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (hyp_ralbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wrex y B ph)) (syn_wrex x A (syn_wrex y B ps))) :=
  by
  have p0000 := @g_rexbii ph ps y B hyp_ralbii_1
  have p0001 := @g_rexbii (syn_wrex y B ph) (syn_wrex y B ps) x A p0000
  exact p0001

@[expose]
noncomputable def g_ralbii2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_ralbii2_1 : Nominal.NPrf
        (syn_wb (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ps))) :
    Nominal.NPrf (syn_wb (syn_wral x A ph) (syn_wral x B ps)) :=
  by
  have p0000 :=
    @g_albii (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ps) x
      hyp_ralbii2_1
  have p0001 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0002 := (Nominal.biimpRefl (syn_wral x B ps))
  have p0003 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) ph))
      (.all x (.imp (.classMem (.cv x) B) ps)) (syn_wral x A ph) (syn_wral x B ps) p0000
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_rexbii2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_rexbii2_1 : Nominal.NPrf
        (syn_wb (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (syn_wrex x B ps)) :=
  by
  have p0000 :=
    @g_exbii (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) ps) x
      hyp_rexbii2_1
  have p0001 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0002 := (Nominal.biimpRefl (syn_wrex x B ps))
  have p0003 :=
    @g_n_3bitr4i (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wex x (syn_wa (.classMem (.cv x) B) ps)) (syn_wrex x A ph) (syn_wrex x B ps)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ralbiia (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralbiia_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wral x A ph) (syn_wral x A ps)) :=
  by
  have p0000 := @g_pm5_74i (.classMem (.cv x) A) ph ps hyp_ralbiia_1
  have p0001 := @g_ralbii2 ph ps x A A p0000
  exact p0001

@[expose]
noncomputable def g_rexbiia (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralbiia_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (syn_wrex x A ps)) :=
  by
  have p0000 := @g_pm5_32i (.classMem (.cv x) A) ph ps hyp_ralbiia_1
  have p0001 := @g_rexbii2 ph ps x A A p0000
  exact p0001

@[expose]
noncomputable def g_r2alf (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (hyp_r2alf_1 : Nominal.NPrf (syn_wnfc y A)) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B ph)) (.all x
          (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := (Nominal.biimpRefl (syn_wral x A (syn_wral y B ph)))
  have p0001 :=
    @g_nfcri y x A
      (by
        first
        | (aesop))
      hyp_r2alf_1
  have p0002 := @g_n_19_21 (.classMem (.cv x) A) (.imp (.classMem (.cv y) B) ph) y p0001
  have p0003 := @g_impexp (.classMem (.cv x) A) (.classMem (.cv y) B) ph
  have p0004 :=
    @g_albii (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)
      (.imp (.classMem (.cv x) A) (.imp (.classMem (.cv y) B) ph)) y p0003
  have p0005 := (Nominal.biimpRefl (syn_wral y B ph))
  have p0006 :=
    @g_imbi2i (syn_wral y B ph) (.all y (.imp (.classMem (.cv y) B) ph))
      (.classMem (.cv x) A) p0005
  have p0007 :=
    @g_n_3bitr4i (.all y (.imp (.classMem (.cv x) A) (.imp (.classMem (.cv y) B) ph)))
      (.imp (.classMem (.cv x) A) (.all y (.imp (.classMem (.cv y) B) ph)))
      (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph))
      (.imp (.classMem (.cv x) A) (syn_wral y B ph)) p0002 p0004 p0006
  have p0008 :=
    @g_albii (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph))
      (.imp (.classMem (.cv x) A) (syn_wral y B ph)) x p0007
  have p0009 :=
    @g_bitr4i (syn_wral x A (syn_wral y B ph))
      (.all x (.imp (.classMem (.cv x) A) (syn_wral y B ph)))
      (.all x (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      p0000 p0008
  exact p0009

@[expose]
noncomputable def g_r2exf (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (hyp_r2alf_1 : Nominal.NPrf (syn_wnfc y A)) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wrex y B ph)) (syn_wex x (syn_wex y
            (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := (Nominal.biimpRefl (syn_wrex x A (syn_wrex y B ph)))
  have p0001 :=
    @g_nfcri y x A
      (by
        first
        | (aesop))
      hyp_r2alf_1
  have p0002 := @g_n_19_42 (.classMem (.cv x) A) (syn_wa (.classMem (.cv y) B) ph) y p0001
  have p0003 := @g_anass (.classMem (.cv x) A) (.classMem (.cv y) B) ph
  have p0004 :=
    @g_exbii (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)
      (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv y) B) ph)) y p0003
  have p0005 := (Nominal.biimpRefl (syn_wrex y B ph))
  have p0006 :=
    @g_anbi2i (syn_wrex y B ph) (syn_wex y (syn_wa (.classMem (.cv y) B) ph))
      (.classMem (.cv x) A) p0005
  have p0007 :=
    @g_n_3bitr4i
      (syn_wex y (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv y) B) ph)))
      (syn_wa (.classMem (.cv x) A) (syn_wex y (syn_wa (.classMem (.cv y) B) ph)))
      (syn_wex y (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph))
      (syn_wa (.classMem (.cv x) A) (syn_wrex y B ph)) p0002 p0004 p0006
  have p0008 :=
    @g_exbii (syn_wex y (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph))
      (syn_wa (.classMem (.cv x) A) (syn_wrex y B ph)) x p0007
  have p0009 :=
    @g_bitr4i (syn_wrex x A (syn_wrex y B ph))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wrex y B ph)))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      p0000 p0008
  exact p0009

@[expose]
noncomputable def g_r2al (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B ph)) (.all x
          (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_r2alf ph x y A B
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_r2ex (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wrex y B ph)) (syn_wex x (syn_wex y
            (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_r2exf ph x y A B
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_n_2ralbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2ralbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf
      (.imp ph (syn_wb (syn_wral x A (syn_wral y B ps)) (syn_wral x A (syn_wral y B ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_ralbidv ph ps ch y B
      (by
        first
        | (aesop))
      hyp_n_2ralbidv_1
  have p0001 :=
    @g_ralbidv ph (syn_wral y B ps) (syn_wral y B ch) x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_n_2rexbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2ralbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf
      (.imp ph (syn_wb (syn_wrex x A (syn_wrex y B ps)) (syn_wrex x A (syn_wrex y B ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rexbidv ph ps ch y B
      (by
        first
        | (aesop))
      hyp_n_2ralbidv_1
  have p0001 :=
    @g_rexbidv ph (syn_wrex y B ps) (syn_wrex y B ch) x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexralbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2ralbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf
      (.imp ph (syn_wb (syn_wrex x A (syn_wral y B ps)) (syn_wrex x A (syn_wral y B ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_ralbidv ph ps ch y B
      (by
        first
        | (aesop))
      hyp_n_2ralbidv_1
  have p0001 :=
    @g_rexbidv ph (syn_wral y B ps) (syn_wral y B ch) x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexanali (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wa ph (.neg ps))) (.neg (syn_wral x A (.imp ph ps)))) :=
  by
  have p0000 := @g_annim ph ps
  have p0001 := @g_rexbii (syn_wa ph (.neg ps)) (.neg (.imp ph ps)) x A p0000
  have p0002 := @g_rexnal (.imp ph ps) x A
  have p0003 :=
    @g_bitri (syn_wrex x A (syn_wa ph (.neg ps))) (syn_wrex x A (.neg (.imp ph ps)))
      (.neg (syn_wral x A (.imp ph ps))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_risset (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A B) (syn_wrex x B (.classEq (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_exancom (.classMem (.cv x) B) (.classEq (.cv x) A) x
  have p0001 := (Nominal.biimpRefl (syn_wrex x B (.classEq (.cv x) A)))
  have p0002 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A B (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0003 :=
    @g_n_3bitr4ri (syn_wex x (syn_wa (.classMem (.cv x) B) (.classEq (.cv x) A)))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) B)))
      (syn_wrex x B (.classEq (.cv x) A)) (.classMem A B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_nfra1 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (syn_wnf x (syn_wral x A ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0001 := @g_nfa1 (.imp (.classMem (.cv x) A) ph) x
  have p0002 :=
    @g_nfxfr (syn_wral x A ph) (.all x (.imp (.classMem (.cv x) A) ph)) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfrald (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_nfrald_2 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfrald_3 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_nfrald_4 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wral y A ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wral y A ps))
  have p0001 := @g_nfcvf x y
  have p0002 :=
    @g_adantl (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnfc x (.cv y)) ph p0001
  have p0003 :=
    @g_adantr ph (syn_wnfc x A) (.neg (.all x (.classEq (.cv x) (.cv y)))) hyp_nfrald_3
  have p0004 :=
    @g_nfeld (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) x (.cv y) A p0002
      p0003
  have p0005 :=
    @g_adantr ph (syn_wnf x ps) (.neg (.all x (.classEq (.cv x) (.cv y)))) hyp_nfrald_4
  have p0006 :=
    @g_nfimd (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) (.classMem (.cv y) A)
      ps x p0004 p0005
  have p0007_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (.neg (.all x (.objEq x y))))
        (syn_wnf x (.imp (.classMem (.cv y) A) ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_nfald2 ph (.imp (.classMem (.cv y) A) ps) x y hyp_nfrald_2 p0007_e01_recanon
  have p0008 :=
    @g_nfxfrd (syn_wral y A ps) (.all y (.imp (.classMem (.cv y) A) ps)) ph x p0000 p0007
  exact p0008

@[expose]
noncomputable def g_nfral (ph : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_nfral_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfral_2 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wnf x (syn_wral y A ph)) :=
  by
  have p0000 := @g_nftru y
  have p0001 := @g_a1i (syn_wnfc x A) syn_wtru hyp_nfral_1
  have p0002 := @g_a1i (syn_wnf x ph) syn_wtru hyp_nfral_2
  have p0003 := @g_nfrald syn_wtru ph x y A p0000 p0001 p0002
  have p0004 := @g_trud (syn_wnf x (syn_wral y A ph)) p0003
  exact p0004

@[expose]
noncomputable def g_nfra2 (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) : Nominal.NPrf (syn_wnf y (syn_wral x A (syn_wral y B ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0001 := @g_nfra1 ph y B
  have p0002 := @g_nfral (syn_wral y B ph) y x A p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfrex (ph : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_nfrex_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfrex_2 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wnf x (syn_wrex y A ph)) :=
  by
  have p0000 := @g_dfrex2 ph y A
  have p0001 := @g_nfn ph x hyp_nfrex_2
  have p0002 := @g_nfral (.neg ph) x y A hyp_nfrex_1 p0001
  have p0003 := @g_nfn (syn_wral y A (.neg ph)) x p0002
  have p0004 := @g_nfxfr (syn_wrex y A ph) (.neg (syn_wral y A (.neg ph))) x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfre1 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (syn_wnf x (syn_wrex x A ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0001 := @g_nfe1 (syn_wa (.classMem (.cv x) A) ph) x
  have p0002 :=
    @g_nfxfr (syn_wrex x A ph) (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rexex (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wrex x A ph) (syn_wex x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0001 := @g_simpr (.classMem (.cv x) A) ph
  have p0002 := @g_eximi (syn_wa (.classMem (.cv x) A) ph) ph x p0001
  have p0003 :=
    @g_sylbi (syn_wrex x A ph) (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wex x ph) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_rsp (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wral x A ph) (.imp (.classMem (.cv x) A) ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0001 := @g_sp (.imp (.classMem (.cv x) A) ph) x
  have p0002 :=
    @g_sylbi (syn_wral x A ph) (.all x (.imp (.classMem (.cv x) A) ph))
      (.imp (.classMem (.cv x) A) ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rspe (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) A) ph) (syn_wrex x A ph)) :=
  by
  have p0000 := @g_n_19_8a (syn_wa (.classMem (.cv x) A) ph) x
  have p0001 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0002 :=
    @g_sylibr (syn_wa (.classMem (.cv x) A) ph)
      (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) (syn_wrex x A ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rsp2 (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wral x A (syn_wral y B ph))
        (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)) :=
  by
  have p0000 := @g_rsp (syn_wral y B ph) x A
  have p0001 := @g_rsp ph y B
  have p0002 :=
    @g_syl6 (syn_wral x A (syn_wral y B ph)) (.classMem (.cv x) A) (syn_wral y B ph)
      (.imp (.classMem (.cv y) B) ph) p0000 p0001
  have p0003 :=
    @g_imp3a (syn_wral x A (syn_wral y B ph)) (.classMem (.cv x) A) (.classMem (.cv y) B)
      ph p0002
  exact p0003

@[expose]
noncomputable def g_rgen (ph : Wff) (x : Var) (A : Class)
    (hyp_rgen_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) ph)) :
    Nominal.NPrf (syn_wral x A ph) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0001 :=
    @g_mpgbir (syn_wral x A ph) (.imp (.classMem (.cv x) A) ph) x p0000 hyp_rgen_1
  exact p0001

@[expose]
noncomputable def g_rgen2a (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (hyp_rgen2a_1 :
      Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) ph)) :
    Nominal.NPrf (syn_wral x A (syn_wral y A ph)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 := @g_eleq1 (.cv y) (.cv x) A
  have p0001 := @g_ex (.classMem (.cv x) A) (.classMem (.cv y) A) ph hyp_rgen2a_1
  have p0002 :=
    @g_syl6bi (.classEq (.cv y) (.cv x)) (.classMem (.cv y) A) (.classMem (.cv x) A)
      (.imp (.classMem (.cv y) A) ph) p0000 p0001
  have p0003 := @g_pm2_43d (.classEq (.cv y) (.cv x)) (.classMem (.cv y) A) ph p0002
  have p0004 :=
    @g_alimi (.classEq (.cv y) (.cv x)) (.imp (.classMem (.cv y) A) ph) y p0003
  have p0005 :=
    @g_a1d (.all y (.classEq (.cv y) (.cv x))) (.all y (.imp (.classMem (.cv y) A) ph))
      (.classMem (.cv x) A) p0004
  have p0006 := @g_eleq1 (.cv z) (.cv x) A
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (syn_wb (.classMem (.cv z) A) (.classMem (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_dvelimv (.classMem (.cv z) A) (.classMem (.cv x) A) y x z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0007_e00_recanon
  have p0008 := @g_alimi (.classMem (.cv x) A) (.imp (.classMem (.cv y) A) ph) y p0001
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.all y (.classEq (.cv y) (.cv x))))
        (.imp (.classMem (.cv x) A) (.all y (.classMem (.cv x) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0009 :=
    @g_syl6 (.neg (.all y (.classEq (.cv y) (.cv x)))) (.classMem (.cv x) A)
      (.all y (.classMem (.cv x) A)) (.all y (.imp (.classMem (.cv y) A) ph))
      p0009_e00_recanon p0008
  have p0010 :=
    @g_pm2_61i (.all y (.classEq (.cv y) (.cv x)))
      (.imp (.classMem (.cv x) A) (.all y (.imp (.classMem (.cv y) A) ph))) p0005 p0009
  have p0011 := (Nominal.biimpRefl (syn_wral y A ph))
  have p0012 :=
    @g_sylibr (.classMem (.cv x) A) (.all y (.imp (.classMem (.cv y) A) ph))
      (syn_wral y A ph) p0010 p0011
  have p0013 := @g_rgen (syn_wral y A ph) x A p0012
  exact p0013

@[expose]
noncomputable def g_rgenw (ph : Wff) (x : Var) (A : Class)
    (hyp_rgenw_1 : Nominal.NPrf ph) : Nominal.NPrf (syn_wral x A ph) :=
  by
  have p0000 := @g_a1i ph (.classMem (.cv x) A) hyp_rgenw_1
  have p0001 := @g_rgen ph x A p0000
  exact p0001

@[expose]
noncomputable def g_rgen2w (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_rgenw_1 : Nominal.NPrf ph) : Nominal.NPrf (syn_wral x A (syn_wral y B ph)) :=
  by
  have p0000 := @g_rgenw ph y B hyp_rgenw_1
  have p0001 := @g_rgenw (syn_wral y B ph) x A p0000
  exact p0001

@[expose]
noncomputable def g_mprg (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_mprg_1 : Nominal.NPrf (.imp (syn_wral x A ph) ps))
    (hyp_mprg_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) ph)) : Nominal.NPrf ps :=
  by
  have p0000 := @g_rgen ph x A hyp_mprg_2
  have p0001 := Nominal.mp p0000 hyp_mprg_1
  exact p0001

@[expose]
noncomputable def g_mprgbir (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_mprgbir_1 : Nominal.NPrf (syn_wb ph (syn_wral x A ps)))
    (hyp_mprgbir_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) ps)) : Nominal.NPrf ph :=
  by
  have p0000 := @g_rgen ps x A hyp_mprgbir_2
  have p0001 := @g_mpbir ph (syn_wral x A ps) p0000 hyp_mprgbir_1
  exact p0001

@[expose]
noncomputable def g_ralim (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (syn_wral x A (.imp ph ps)) (.imp (syn_wral x A ph) (syn_wral x A ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wral x A (.imp ph ps)))
  have p0001 := Nominal.ax2 (.classMem (.cv x) A) ph ps
  have p0002 :=
    @g_al2imi (.imp (.classMem (.cv x) A) (.imp ph ps)) (.imp (.classMem (.cv x) A) ph)
      (.imp (.classMem (.cv x) A) ps) x p0001
  have p0003 :=
    @g_sylbi (syn_wral x A (.imp ph ps))
      (.all x (.imp (.classMem (.cv x) A) (.imp ph ps)))
      (.imp (.all x (.imp (.classMem (.cv x) A) ph)) (.all x (.imp (.classMem (.cv x) A) ps)))
      p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0005 := (Nominal.biimpRefl (syn_wral x A ps))
  have p0006 :=
    @g_n_3imtr4g (syn_wral x A (.imp ph ps)) (.all x (.imp (.classMem (.cv x) A) ph))
      (.all x (.imp (.classMem (.cv x) A) ps)) (syn_wral x A ph) (syn_wral x A ps) p0003
      p0004 p0005
  exact p0006

@[expose]
noncomputable def g_ralimi2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_ralimi2_1 : Nominal.NPrf
        (.imp (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ps))) :
    Nominal.NPrf (.imp (syn_wral x A ph) (syn_wral x B ps)) :=
  by
  have p0000 :=
    @g_alimi (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ps) x
      hyp_ralimi2_1
  have p0001 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0002 := (Nominal.biimpRefl (syn_wral x B ps))
  have p0003 :=
    @g_n_3imtr4i (.all x (.imp (.classMem (.cv x) A) ph))
      (.all x (.imp (.classMem (.cv x) B) ps)) (syn_wral x A ph) (syn_wral x B ps) p0000
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ralimia (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralimia_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.imp ph ps))) :
    Nominal.NPrf (.imp (syn_wral x A ph) (syn_wral x A ps)) :=
  by
  have p0000 := @g_a2i (.classMem (.cv x) A) ph ps hyp_ralimia_1
  have p0001 := @g_ralimi2 ph ps x A A p0000
  exact p0001

@[expose]
noncomputable def g_ralimiaa (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralimiaa_1 : Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) A) ph) ps)) :
    Nominal.NPrf (.imp (syn_wral x A ph) (syn_wral x A ps)) :=
  by
  have p0000 := @g_ex (.classMem (.cv x) A) ph ps hyp_ralimiaa_1
  have p0001 := @g_ralimia ph ps x A p0000
  exact p0001

@[expose]
noncomputable def g_ralimi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralimi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wral x A ph) (syn_wral x A ps)) :=
  by
  have p0000 := @g_a1i (.imp ph ps) (.classMem (.cv x) A) hyp_ralimi_1
  have p0001 := @g_ralimia ph ps x A p0000
  exact p0001

@[expose]
noncomputable def g_ral2imi (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ral2imi_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (syn_wral x A ph) (.imp (syn_wral x A ps) (syn_wral x A ch))) :=
  by
  have p0000 := @g_ralimi ph (.imp ps ch) x A hyp_ral2imi_1
  have p0001 := @g_ralim ps ch x A
  have p0002 :=
    @g_syl (syn_wral x A ph) (syn_wral x A (.imp ps ch))
      (.imp (syn_wral x A ps) (syn_wral x A ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ralimdaa (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralimdaa_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_ralimdaa_2 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wral x A ps) (syn_wral x A ch))) :=
  by
  have p0000 := @g_ex ph (.classMem (.cv x) A) (.imp ps ch) hyp_ralimdaa_2
  have p0001 := @g_a2d ph (.classMem (.cv x) A) ps ch p0000
  have p0002 :=
    @g_alimd ph (.imp (.classMem (.cv x) A) ps) (.imp (.classMem (.cv x) A) ch) x
      hyp_ralimdaa_1 p0001
  have p0003 := (Nominal.biimpRefl (syn_wral x A ps))
  have p0004 := (Nominal.biimpRefl (syn_wral x A ch))
  have p0005 :=
    @g_n_3imtr4g ph (.all x (.imp (.classMem (.cv x) A) ps))
      (.all x (.imp (.classMem (.cv x) A) ch)) (syn_wral x A ps) (syn_wral x A ch) p0002
      p0003 p0004
  exact p0005

@[expose]
noncomputable def g_ralimdva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralimdva_1 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wral x A ps) (syn_wral x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_ralimdaa ph ps ch x A p0000 hyp_ralimdva_1
  exact p0001

@[expose]
noncomputable def g_ralimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wral x A ps) (syn_wral x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_adantr ph (.imp ps ch) (.classMem (.cv x) A) hyp_ralimdv_1
  have p0001 :=
    @g_ralimdva ph ps ch x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_ralrimi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralrimi_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_ralrimi_2 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) ps))) :
    Nominal.NPrf (.imp ph (syn_wral x A ps)) :=
  by
  have p0000 := @g_alrimi ph (.imp (.classMem (.cv x) A) ps) x hyp_ralrimi_1 hyp_ralrimi_2
  have p0001 := (Nominal.biimpRefl (syn_wral x A ps))
  have p0002 :=
    @g_sylibr ph (.all x (.imp (.classMem (.cv x) A) ps)) (syn_wral x A ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ralrimiv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralrimiv_1 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) ps))) :
    Nominal.NPrf (.imp ph (syn_wral x A ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_ralrimi ph ps x A p0000 hyp_ralrimiv_1
  exact p0001

@[expose]
noncomputable def g_ralrimiva (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralrimiva_1 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) ps)) :
    Nominal.NPrf (.imp ph (syn_wral x A ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_ex ph (.classMem (.cv x) A) ps hyp_ralrimiva_1
  have p0001 :=
    @g_ralrimiv ph ps x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_ralrimivw (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralrimivw_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp ph (syn_wral x A ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_a1d ph ps (.classMem (.cv x) A) hyp_ralrimivw_1
  have p0001 :=
    @g_ralrimiv ph ps x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_r19_21t (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (syn_wnf x ph) (syn_wb (syn_wral x A (.imp ph ps)) (.imp ph (syn_wral x A ps)))) :=
  by
  have p0000 := @g_bi2_04 (.classMem (.cv x) A) ph ps
  have p0001 :=
    @g_albii (.imp (.classMem (.cv x) A) (.imp ph ps))
      (.imp ph (.imp (.classMem (.cv x) A) ps)) x p0000
  have p0002 := @g_n_19_21t ph (.imp (.classMem (.cv x) A) ps) x
  have p0003 :=
    @g_syl5bb (.all x (.imp (.classMem (.cv x) A) (.imp ph ps)))
      (.all x (.imp ph (.imp (.classMem (.cv x) A) ps))) (syn_wnf x ph)
      (.imp ph (.all x (.imp (.classMem (.cv x) A) ps))) p0001 p0002
  have p0004 := (Nominal.biimpRefl (syn_wral x A (.imp ph ps)))
  have p0005 := (Nominal.biimpRefl (syn_wral x A ps))
  have p0006 :=
    @g_imbi2i (syn_wral x A ps) (.all x (.imp (.classMem (.cv x) A) ps)) ph p0005
  have p0007 :=
    @g_n_3bitr4g (syn_wnf x ph) (.all x (.imp (.classMem (.cv x) A) (.imp ph ps)))
      (.imp ph (.all x (.imp (.classMem (.cv x) A) ps))) (syn_wral x A (.imp ph ps))
      (.imp ph (syn_wral x A ps)) p0003 p0004 p0006
  exact p0007

@[expose]
noncomputable def g_r19_21 (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_r19_21_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (syn_wral x A (.imp ph ps)) (.imp ph (syn_wral x A ps))) :=
  by
  have p0000 := @g_r19_21t ph ps x A
  have p0001 := Nominal.mp hyp_r19_21_1 p0000
  exact p0001

@[expose]
noncomputable def g_r19_21v (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wb (syn_wral x A (.imp ph ps)) (.imp ph (syn_wral x A ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_r19_21 ph ps x A p0000
  exact p0001

@[expose]
noncomputable def g_ralrimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralrimd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_ralrimd_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_ralrimd_3 : Nominal.NPrf (.imp ph (.imp ps (.imp (.classMem (.cv x) A) ch)))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wral x A ch))) :=
  by
  have p0000 :=
    @g_alrimd ph ps (.imp (.classMem (.cv x) A) ch) x hyp_ralrimd_1 hyp_ralrimd_2
      hyp_ralrimd_3
  have p0001 := (Nominal.biimpRefl (syn_wral x A ch))
  have p0002 :=
    @g_syl6ibr ph ps (.all x (.imp (.classMem (.cv x) A) ch)) (syn_wral x A ch) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_ralrimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ralrimdv_1 : Nominal.NPrf (.imp ph (.imp ps (.imp (.classMem (.cv x) A) ch)))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wral x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 := @g_ralrimd ph ps ch x A p0000 p0001 hyp_ralrimdv_1
  exact p0002

@[expose]
noncomputable def g_ralrimivv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y)
    (hyp_ralrimivv_1 : Nominal.NPrf
        (.imp ph (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ps))) :
    Nominal.NPrf (.imp ph (syn_wral x A (syn_wral y B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_exp3a ph (.classMem (.cv x) A) (.classMem (.cv y) B) ps hyp_ralrimivv_1
  have p0001 :=
    @g_ralrimdv ph (.classMem (.cv x) A) ps y B
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0000
  have p0002 :=
    @g_ralrimiv ph (syn_wral y B ps) x A
      (by
        first
        | (aesop))
      p0001
  exact p0002

@[expose]
noncomputable def g_ralrimivva (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y)
    (hyp_ralrimivva_1 : Nominal.NPrf
        (.imp (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) ps)) :
    Nominal.NPrf (.imp ph (syn_wral x A (syn_wral y B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_ex ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ps hyp_ralrimivva_1
  have p0001 :=
    @g_ralrimivv ph ps x y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_ralrimdvv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralrimdvv_1 : Nominal.NPrf (.imp ph
          (.imp ps (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ch)))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wral x A (syn_wral y B ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_imp ph ps (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ch)
      hyp_ralrimdvv_1
  have p0001 :=
    @g_ralrimivv (syn_wa ph ps) ch x y A B
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_ex ph ps (syn_wral x A (syn_wral y B ch)) p0001
  exact p0002

@[expose]
noncomputable def g_rgen2 (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_rgen2_1 :
      Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)) :
    Nominal.NPrf (syn_wral x A (syn_wral y B ph)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_ralrimiva (.classMem (.cv x) A) ph y B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      hyp_rgen2_1
  have p0001 := @g_rgen (syn_wral y B ph) x A p0000
  exact p0001

@[expose]
noncomputable def g_r19_21bi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_r19_21bi_1 : Nominal.NPrf (.imp ph (syn_wral x A ps))) :
    Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) ps) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wral x A ps))
  have p0001 :=
    @g_sylib ph (syn_wral x A ps) (.all x (.imp (.classMem (.cv x) A) ps)) hyp_r19_21bi_1
      p0000
  have p0002 := @g_n_19_21bi ph (.imp (.classMem (.cv x) A) ps) x p0001
  have p0003 := @g_imp ph (.classMem (.cv x) A) ps p0002
  exact p0003

@[expose]
noncomputable def g_nrex (ps : Wff) (x : Var) (A : Class)
    (hyp_nrex_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.neg ps))) :
    Nominal.NPrf (.neg (syn_wrex x A ps)) :=
  by
  have p0000 := @g_rgen (.neg ps) x A hyp_nrex_1
  have p0001 := @g_ralnex ps x A
  have p0002 := @g_mpbi (syn_wral x A (.neg ps)) (.neg (syn_wrex x A ps)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nrexdv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_nrexdv_1 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (syn_wrex x A ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_ralrimiva ph (.neg ps) x A
      (by
        first
        | (aesop))
      hyp_nrexdv_1
  have p0001 := @g_ralnex ps x A
  have p0002 := @g_sylib ph (syn_wral x A (.neg ps)) (.neg (syn_wrex x A ps)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rexim (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (syn_wral x A (.imp ph ps)) (.imp (syn_wrex x A ph) (syn_wrex x A ps))) :=
  by
  have p0000 := @g_con3 ph ps
  have p0001 := @g_ral2imi (.imp ph ps) (.neg ps) (.neg ph) x A p0000
  have p0002 :=
    @g_con3d (syn_wral x A (.imp ph ps)) (syn_wral x A (.neg ps)) (syn_wral x A (.neg ph))
      p0001
  have p0003 := @g_dfrex2 ph x A
  have p0004 := @g_dfrex2 ps x A
  have p0005 :=
    @g_n_3imtr4g (syn_wral x A (.imp ph ps)) (.neg (syn_wral x A (.neg ph)))
      (.neg (syn_wral x A (.neg ps))) (syn_wrex x A ph) (syn_wrex x A ps) p0002 p0003
      p0004
  exact p0005

@[expose]
noncomputable def g_reximia (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_reximia_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.imp ph ps))) :
    Nominal.NPrf (.imp (syn_wrex x A ph) (syn_wrex x A ps)) :=
  by
  have p0000 := @g_rexim ph ps x A
  have p0001 :=
    @g_mprg (.imp ph ps) (.imp (syn_wrex x A ph) (syn_wrex x A ps)) x A p0000
      hyp_reximia_1
  exact p0001

@[expose]
noncomputable def g_reximi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_reximi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wrex x A ph) (syn_wrex x A ps)) :=
  by
  have p0000 := @g_a1i (.imp ph ps) (.classMem (.cv x) A) hyp_reximi_1
  have p0001 := @g_reximia ph ps x A p0000
  exact p0001

@[expose]
noncomputable def g_reximdai (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_reximdai_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_reximdai_2 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) (syn_wrex x A ch))) :=
  by
  have p0000 := @g_ralrimi ph (.imp ps ch) x A hyp_reximdai_1 hyp_reximdai_2
  have p0001 := @g_rexim ps ch x A
  have p0002 :=
    @g_syl ph (syn_wral x A (.imp ps ch)) (.imp (syn_wrex x A ps) (syn_wrex x A ch)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_reximdvai (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_reximdvai_1 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) (syn_wrex x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_reximdai ph ps ch x A p0000 hyp_reximdvai_1
  exact p0001

@[expose]
noncomputable def g_reximdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_reximdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) (syn_wrex x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_a1d ph (.imp ps ch) (.classMem (.cv x) A) hyp_reximdv_1
  have p0001 :=
    @g_reximdvai ph ps ch x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_reximdva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_reximdva_1 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) (syn_wrex x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_ex ph (.classMem (.cv x) A) (.imp ps ch) hyp_reximdva_1
  have p0001 :=
    @g_reximdvai ph ps ch x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_r19_23t (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (syn_wnf x ps) (syn_wb (syn_wral x A (.imp ph ps)) (.imp (syn_wrex x A ph) ps))) :=
  by
  have p0000 := @g_n_19_23t (syn_wa (.classMem (.cv x) A) ph) ps x
  have p0001 := (Nominal.biimpRefl (syn_wral x A (.imp ph ps)))
  have p0002 := @g_impexp (.classMem (.cv x) A) ph ps
  have p0003 :=
    @g_albii (.imp (syn_wa (.classMem (.cv x) A) ph) ps)
      (.imp (.classMem (.cv x) A) (.imp ph ps)) x p0002
  have p0004 :=
    @g_bitr4i (syn_wral x A (.imp ph ps))
      (.all x (.imp (.classMem (.cv x) A) (.imp ph ps)))
      (.all x (.imp (syn_wa (.classMem (.cv x) A) ph) ps)) p0001 p0003
  have p0005 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0006 :=
    @g_imbi1i (syn_wrex x A ph) (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) ps p0005
  have p0007 :=
    @g_n_3bitr4g (syn_wnf x ps) (.all x (.imp (syn_wa (.classMem (.cv x) A) ph) ps))
      (.imp (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) ps) (syn_wral x A (.imp ph ps))
      (.imp (syn_wrex x A ph) ps) p0000 p0004 p0006
  exact p0007

@[expose]
noncomputable def g_r19_23 (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_r19_23_1 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wb (syn_wral x A (.imp ph ps)) (.imp (syn_wrex x A ph) ps)) :=
  by
  have p0000 := @g_r19_23t ph ps x A
  have p0001 := Nominal.mp hyp_r19_23_1 p0000
  exact p0001

@[expose]
noncomputable def g_r19_23v (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (syn_wb (syn_wral x A (.imp ph ps)) (.imp (syn_wrex x A ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_r19_23 ph ps x A p0000
  exact p0001

@[expose]
noncomputable def g_rexlimi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_rexlimi_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_rexlimi_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.imp ph ps))) :
    Nominal.NPrf (.imp (syn_wrex x A ph) ps) :=
  by
  have p0000 := @g_rgen (.imp ph ps) x A hyp_rexlimi_2
  have p0001 := @g_r19_23 ph ps x A hyp_rexlimi_1
  have p0002 :=
    @g_mpbi (syn_wral x A (.imp ph ps)) (.imp (syn_wrex x A ph) ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rexlimiv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv)
    (hyp_rexlimiv_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.imp ph ps))) :
    Nominal.NPrf (.imp (syn_wrex x A ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_rexlimi ph ps x A p0000 hyp_rexlimiv_1
  exact p0001

@[expose]
noncomputable def g_rexlimiva (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv)
    (hyp_rexlimiva_1 : Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) A) ph) ps)) :
    Nominal.NPrf (.imp (syn_wrex x A ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_ex (.classMem (.cv x) A) ph ps hyp_rexlimiva_1
  have p0001 :=
    @g_rexlimiv ph ps x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexlimivw (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv) (hyp_rexlimivw_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wrex x A ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_a1i (.imp ph ps) (.classMem (.cv x) A) hyp_rexlimivw_1
  have p0001 :=
    @g_rexlimiv ph ps x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexlimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_rexlimd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_rexlimd_2 : Nominal.NPrf (syn_wnf x ch))
    (hyp_rexlimd_3 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) ch)) :=
  by
  have p0000 := @g_ralrimi ph (.imp ps ch) x A hyp_rexlimd_1 hyp_rexlimd_3
  have p0001 := @g_r19_23 ps ch x A hyp_rexlimd_2
  have p0002 :=
    @g_sylib ph (syn_wral x A (.imp ps ch)) (.imp (syn_wrex x A ps) ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rexlimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdv_1 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) ch)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ch x
      (by
        first
        | (aesop))
  have p0002 := @g_rexlimd ph ps ch x A p0000 p0001 hyp_rexlimdv_1
  exact p0002

@[expose]
noncomputable def g_rexlimdva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdva_1 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) ch)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_ex ph (.classMem (.cv x) A) (.imp ps ch) hyp_rexlimdva_1
  have p0001 :=
    @g_rexlimdv ph ps ch x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexlimdvaa (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdvaa_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa (.classMem (.cv x) A) ps)) ch)) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) ch)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_expr ph (.classMem (.cv x) A) ps ch hyp_rexlimdvaa_1
  have p0001 :=
    @g_rexlimdva ph ps ch x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexlimdv3a (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdv3a_1 : Nominal.NPrf (.imp (syn_w3a ph (.classMem (.cv x) A) ps) ch)) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) ch)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_n_3exp ph (.classMem (.cv x) A) ps ch hyp_rexlimdv3a_1
  have p0001 :=
    @g_rexlimdv ph ps ch x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexlimdvw (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdvw_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A ps) ch)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_a1d ph (.imp ps ch) (.classMem (.cv x) A) hyp_rexlimdvw_1
  have p0001 :=
    @g_rexlimdv ph ps ch x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexlimddv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimddv_1 : Nominal.NPrf (.imp ph (syn_wrex x A ps)))
    (hyp_rexlimddv_2 : Nominal.NPrf (.imp (syn_wa ph (syn_wa (.classMem (.cv x) A) ps)) ch)) :
    Nominal.NPrf (.imp ph ch) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_rexlimdvaa ph ps ch x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_rexlimddv_2
  have p0001 := @g_mpd ph (syn_wrex x A ps) ch hyp_rexlimddv_1 p0000
  exact p0001

@[expose]
noncomputable def g_rexlimivv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_rexlimivv_1 : Nominal.NPrf
        (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.imp ph ps))) :
    Nominal.NPrf (.imp (syn_wrex x A (syn_wrex y B ph)) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rexlimdva (.classMem (.cv x) A) ph ps y B
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      hyp_rexlimivv_1
  have p0001 :=
    @g_rexlimiv (syn_wrex y B ph) ps x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rexlimdvv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ch_y : y ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_rexlimdvv_1 : Nominal.NPrf (.imp ph
          (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A (syn_wrex y B ps)) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_expdimp ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.imp ps ch) hyp_rexlimdvv_1
  have p0001 :=
    @g_rexlimdv (syn_wa ph (.classMem (.cv x) A)) ps ch y B
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0000
  have p0002 :=
    @g_rexlimdva ph (syn_wrex y B ps) ch x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0001
  exact p0002

@[expose]
noncomputable def g_rexlimdvva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ch_y : y ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_rexlimdvva_1 : Nominal.NPrf
        (.imp (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wrex x A (syn_wrex y B ps)) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_ex ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.imp ps ch)
      hyp_rexlimdvva_1
  have p0001 :=
    @g_rexlimdvv ph ps ch x y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_r19_26 (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wa ph ps)) (syn_wa (syn_wral x A ph) (syn_wral x A ps))) :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := @g_ralimi (syn_wa ph ps) ph x A p0000
  have p0002 := @g_simpr ph ps
  have p0003 := @g_ralimi (syn_wa ph ps) ps x A p0002
  have p0004 :=
    @g_jca (syn_wral x A (syn_wa ph ps)) (syn_wral x A ph) (syn_wral x A ps) p0001 p0003
  have p0005 := @g_pm3_2 ph ps
  have p0006 := @g_ral2imi ph ps (syn_wa ph ps) x A p0005
  have p0007 :=
    @g_imp (syn_wral x A ph) (syn_wral x A ps) (syn_wral x A (syn_wa ph ps)) p0006
  have p0008 :=
    @g_impbii (syn_wral x A (syn_wa ph ps)) (syn_wa (syn_wral x A ph) (syn_wral x A ps))
      p0004 p0007
  exact p0008

@[expose]
noncomputable def g_r19_26_2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B (syn_wa ph ps)))
        (syn_wa (syn_wral x A (syn_wral y B ph)) (syn_wral x A (syn_wral y B ps)))) :=
  by
  have p0000 := @g_r19_26 ph ps y B
  have p0001 :=
    @g_ralbii (syn_wral y B (syn_wa ph ps)) (syn_wa (syn_wral y B ph) (syn_wral y B ps)) x
      A p0000
  have p0002 := @g_r19_26 (syn_wral y B ph) (syn_wral y B ps) x A
  have p0003 :=
    @g_bitri (syn_wral x A (syn_wral y B (syn_wa ph ps)))
      (syn_wral x A (syn_wa (syn_wral y B ph) (syn_wral y B ps)))
      (syn_wa (syn_wral x A (syn_wral y B ph)) (syn_wral x A (syn_wral y B ps))) p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_ralbiim (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wb ph ps))
        (syn_wa (syn_wral x A (.imp ph ps)) (syn_wral x A (.imp ps ph)))) :=
  by
  have p0000 := @g_dfbi2 ph ps
  have p0001 := @g_ralbii (syn_wb ph ps) (syn_wa (.imp ph ps) (.imp ps ph)) x A p0000
  have p0002 := @g_r19_26 (.imp ph ps) (.imp ps ph) x A
  have p0003 :=
    @g_bitri (syn_wral x A (syn_wb ph ps))
      (syn_wral x A (syn_wa (.imp ph ps) (.imp ps ph)))
      (syn_wa (syn_wral x A (.imp ph ps)) (syn_wral x A (.imp ps ph))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_r19_27av (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wral x A ph) ps) (syn_wral x A (syn_wa ph ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := Nominal.ax1 ps (.classMem (.cv x) A)
  have p0001 :=
    @g_ralrimiv ps ps x A
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_anim2i ps (syn_wral x A ps) (syn_wral x A ph) p0001
  have p0003 := @g_r19_26 ph ps x A
  have p0004 :=
    @g_sylibr (syn_wa (syn_wral x A ph) ps) (syn_wa (syn_wral x A ph) (syn_wral x A ps))
      (syn_wral x A (syn_wa ph ps)) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_r19_28av (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wral x A ps)) (syn_wral x A (syn_wa ph ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_r19_27av ps ph x A
      (by
        first
        | (aesop))
  have p0001 := @g_ancom ph (syn_wral x A ps)
  have p0002 := @g_ancom ph ps
  have p0003 := @g_ralbii (syn_wa ph ps) (syn_wa ps ph) x A p0002
  have p0004 :=
    @g_n_3imtr4i (syn_wa (syn_wral x A ps) ph) (syn_wral x A (syn_wa ps ph))
      (syn_wa ph (syn_wral x A ps)) (syn_wral x A (syn_wa ph ps)) p0000 p0001 p0003
  exact p0004

@[expose]
noncomputable def g_r19_29 (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wral x A ph) (syn_wrex x A ps)) (syn_wrex x A (syn_wa ph ps))) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @g_ralimi ph (.imp ps (syn_wa ph ps)) x A p0000
  have p0002 := @g_rexim ps (syn_wa ph ps) x A
  have p0003 :=
    @g_syl (syn_wral x A ph) (syn_wral x A (.imp ps (syn_wa ph ps)))
      (.imp (syn_wrex x A ps) (syn_wrex x A (syn_wa ph ps))) p0001 p0002
  have p0004 :=
    @g_imp (syn_wral x A ph) (syn_wrex x A ps) (syn_wrex x A (syn_wa ph ps)) p0003
  exact p0004

@[expose]
noncomputable def g_r19_35 (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (.imp ph ps)) (.imp (syn_wral x A ph) (syn_wrex x A ps))) :=
  by
  have p0000 := @g_r19_26 ph (.neg ps) x A
  have p0001 := @g_annim ph ps
  have p0002 := @g_ralbii (syn_wa ph (.neg ps)) (.neg (.imp ph ps)) x A p0001
  have p0003 := (Nominal.biimpRefl (syn_wa (syn_wral x A ph) (syn_wral x A (.neg ps))))
  have p0004 :=
    @g_n_3bitr3i (syn_wral x A (syn_wa ph (.neg ps)))
      (syn_wa (syn_wral x A ph) (syn_wral x A (.neg ps)))
      (syn_wral x A (.neg (.imp ph ps)))
      (.neg (.imp (syn_wral x A ph) (.neg (syn_wral x A (.neg ps))))) p0000 p0002 p0003
  have p0005 :=
    @g_con2bii (syn_wral x A (.neg (.imp ph ps)))
      (.imp (syn_wral x A ph) (.neg (syn_wral x A (.neg ps)))) p0004
  have p0006 := @g_dfrex2 ps x A
  have p0007 :=
    @g_imbi2i (syn_wrex x A ps) (.neg (syn_wral x A (.neg ps))) (syn_wral x A ph) p0006
  have p0008 := @g_dfrex2 (.imp ph ps) x A
  have p0009 :=
    @g_n_3bitr4ri (.imp (syn_wral x A ph) (.neg (syn_wral x A (.neg ps))))
      (.neg (syn_wral x A (.neg (.imp ph ps)))) (.imp (syn_wral x A ph) (syn_wrex x A ps))
      (syn_wrex x A (.imp ph ps)) p0005 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_r19_41 (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_r19_41_1 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wb (syn_wrex x A (syn_wa ph ps)) (syn_wa (syn_wrex x A ph) ps)) :=
  by
  have p0000 := @g_anass (.classMem (.cv x) A) ph ps
  have p0001 :=
    @g_exbii (syn_wa (syn_wa (.classMem (.cv x) A) ph) ps)
      (syn_wa (.classMem (.cv x) A) (syn_wa ph ps)) x p0000
  have p0002 := @g_n_19_41 (syn_wa (.classMem (.cv x) A) ph) ps x hyp_r19_41_1
  have p0003 :=
    @g_bitr3i (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wa ph ps)))
      (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) ph) ps))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) ps) p0001 p0002
  have p0004 := (Nominal.biimpRefl (syn_wrex x A (syn_wa ph ps)))
  have p0005 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0006 :=
    @g_anbi1i (syn_wrex x A ph) (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) ps p0005
  have p0007 :=
    @g_n_3bitr4i (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wa ph ps)))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) ps)
      (syn_wrex x A (syn_wa ph ps)) (syn_wa (syn_wrex x A ph) ps) p0003 p0004 p0006
  exact p0007

@[expose]
noncomputable def g_r19_41v (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (syn_wb (syn_wrex x A (syn_wa ph ps)) (syn_wa (syn_wrex x A ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_r19_41 ph ps x A p0000
  exact p0001

@[expose]
noncomputable def g_r19_42v (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wb (syn_wrex x A (syn_wa ph ps)) (syn_wa ph (syn_wrex x A ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_r19_41v ps ph x A
      (by
        first
        | (aesop))
  have p0001 := @g_ancom ph ps
  have p0002 := @g_rexbii (syn_wa ph ps) (syn_wa ps ph) x A p0001
  have p0003 := @g_ancom ph (syn_wrex x A ps)
  have p0004 :=
    @g_n_3bitr4i (syn_wrex x A (syn_wa ps ph)) (syn_wa (syn_wrex x A ps) ph)
      (syn_wrex x A (syn_wa ph ps)) (syn_wa ph (syn_wrex x A ps)) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_r19_43 (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wo ph ps)) (syn_wo (syn_wrex x A ph) (syn_wrex x A ps))) :=
  by
  have p0000 := @g_r19_35 (.neg ph) ps x A
  have p0001 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0002 := @g_rexbii (syn_wo ph ps) (.imp (.neg ph) ps) x A p0001
  have p0003 := (Nominal.biimpRefl (syn_wo (syn_wrex x A ph) (syn_wrex x A ps)))
  have p0004 := @g_ralnex ph x A
  have p0005 :=
    @g_imbi1i (syn_wral x A (.neg ph)) (.neg (syn_wrex x A ph)) (syn_wrex x A ps) p0004
  have p0006 :=
    @g_bitr4i (syn_wo (syn_wrex x A ph) (syn_wrex x A ps))
      (.imp (.neg (syn_wrex x A ph)) (syn_wrex x A ps))
      (.imp (syn_wral x A (.neg ph)) (syn_wrex x A ps)) p0003 p0005
  have p0007 :=
    @g_n_3bitr4i (syn_wrex x A (.imp (.neg ph) ps))
      (.imp (syn_wral x A (.neg ph)) (syn_wrex x A ps)) (syn_wrex x A (syn_wo ph ps))
      (syn_wo (syn_wrex x A ph) (syn_wrex x A ps)) p0000 p0002 p0006
  exact p0007

@[expose]
noncomputable def g_ralcomf (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (hyp_ralcomf_1 : Nominal.NPrf (syn_wnfc y A))
    (hyp_ralcomf_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B ph)) (syn_wral y B (syn_wral x A ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_ancomsimp (.classMem (.cv x) A) (.classMem (.cv y) B) ph
  have p0001 :=
    @g_n_2albii (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)
      (.imp (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph) x y p0000
  have p0002 :=
    @g_alcom (.imp (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph) x y
  have p0003 :=
    @g_bitri
      (.all x (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      (.all x (.all y (.imp (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      (.all y (.all x (.imp (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      p0001 p0002
  have p0004 :=
    @g_r2alf ph x y A B
      (by
        first
        | (aesop))
      hyp_ralcomf_1
  have p0005 :=
    @g_r2alf ph y x B A
      (by
        first
        | (aesop))
      hyp_ralcomf_2
  have p0006 :=
    @g_n_3bitr4i
      (.all x (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      (.all y (.all x (.imp (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      (syn_wral x A (syn_wral y B ph)) (syn_wral y B (syn_wral x A ph)) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_rexcomf (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (hyp_ralcomf_1 : Nominal.NPrf (syn_wnfc y A))
    (hyp_ralcomf_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wrex y B ph)) (syn_wrex y B (syn_wrex x A ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_ancom (.classMem (.cv x) A) (.classMem (.cv y) B)
  have p0001 :=
    @g_anbi1i (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph p0000
  have p0002 :=
    @g_n_2exbii (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)
      (syn_wa (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph) x y p0001
  have p0003 :=
    @g_excom (syn_wa (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph) x y
  have p0004 :=
    @g_bitri
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      (syn_wex y (syn_wex x (syn_wa (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      p0002 p0003
  have p0005 :=
    @g_r2exf ph x y A B
      (by
        first
        | (aesop))
      hyp_ralcomf_1
  have p0006 :=
    @g_r2exf ph y x B A
      (by
        first
        | (aesop))
      hyp_ralcomf_2
  have p0007 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      (syn_wex y (syn_wex x (syn_wa (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      (syn_wrex x A (syn_wrex y B ph)) (syn_wrex y B (syn_wrex x A ph)) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_ralcom (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B ph)) (syn_wral y B (syn_wral x A ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv x B
      (by
        first
        | (aesop))
  have p0002 :=
    @g_ralcomf ph x y A B
      (by
        first
        | (aesop))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rexcom (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wrex y B ph)) (syn_wrex y B (syn_wrex x A ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv x B
      (by
        first
        | (aesop))
  have p0002 :=
    @g_rexcomf ph x y A B
      (by
        first
        | (aesop))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_reean (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_reean_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_reean_2 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wrex y B (syn_wa ph ps)))
        (syn_wa (syn_wrex x A ph) (syn_wrex y B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_an4 (.classMem (.cv x) A) (.classMem (.cv y) B) ph ps
  have p0001 :=
    @g_n_2exbii
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa ph ps))
      (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) B) ps)) x y
      p0000
  have p0002 :=
    @g_nfv (.classMem (.cv x) A) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 := @g_nfan (.classMem (.cv x) A) ph y p0002 hyp_reean_1
  have p0004 :=
    @g_nfv (.classMem (.cv y) B) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @g_nfan (.classMem (.cv y) B) ps x p0004 hyp_reean_2
  have p0006 :=
    @g_eean (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) B) ps) x y p0003
      p0005
  have p0007 :=
    @g_bitri
      (syn_wex x (syn_wex y
          (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa ph ps))))
      (syn_wex x (syn_wex y
          (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) B) ps))))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
        (syn_wex y (syn_wa (.classMem (.cv y) B) ps)))
      p0001 p0006
  have p0008 :=
    @g_r2ex (syn_wa ph ps) x y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0009 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0010 := (Nominal.biimpRefl (syn_wrex y B ps))
  have p0011 :=
    @g_anbi12i (syn_wrex x A ph) (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wrex y B ps) (syn_wex y (syn_wa (.classMem (.cv y) B) ps)) p0009 p0010
  have p0012 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wex y
          (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa ph ps))))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
        (syn_wex y (syn_wa (.classMem (.cv y) B) ps)))
      (syn_wrex x A (syn_wrex y B (syn_wa ph ps)))
      (syn_wa (syn_wrex x A ph) (syn_wrex y B ps)) p0007 p0008 p0011
  exact p0012

@[expose]
noncomputable def g_reeanv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wrex x A (syn_wrex y B (syn_wa ph ps)))
        (syn_wa (syn_wrex x A ph) (syn_wrex y B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 :=
    @g_reean ph ps x y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rabid2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classEq A (syn_crab x A ph)) (syn_wral x A ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_eqabb (syn_wa (.classMem (.cv x) A) ph) x A
      (by
        first
        | (aesop))
  have p0001 := @g_pm4_71 (.classMem (.cv x) A) ph
  have p0002 :=
    @g_albii (.imp (.classMem (.cv x) A) ph)
      (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) ph)) x p0001
  have p0003 :=
    @g_bitr4i (.classEq A (.cab x (syn_wa (.classMem (.cv x) A) ph)))
      (.all x (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) ph)))
      (.all x (.imp (.classMem (.cv x) A) ph)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (syn_crab x A ph))
  have p0005 :=
    @g_eqeq2i (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph)) A p0004
  have p0006 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0007 :=
    @g_n_3bitr4i (.classEq A (.cab x (syn_wa (.classMem (.cv x) A) ph)))
      (.all x (.imp (.classMem (.cv x) A) ph)) (.classEq A (syn_crab x A ph))
      (syn_wral x A ph) p0003 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_rabbi (ps : Wff) (ch : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wb ps ch)) (.classEq (syn_crab x A ps) (syn_crab x A ch))) :=
  by
  have p0000 :=
    @g_abbib (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv x) A) ch) x
  have p0001 := (Nominal.classEqRefl (syn_crab x A ps))
  have p0002 := (Nominal.classEqRefl (syn_crab x A ch))
  have p0003 :=
    @g_eqeq12i (syn_crab x A ps) (.cab x (syn_wa (.classMem (.cv x) A) ps))
      (syn_crab x A ch) (.cab x (syn_wa (.classMem (.cv x) A) ch)) p0001 p0002
  have p0004 := (Nominal.biimpRefl (syn_wral x A (syn_wb ps ch)))
  have p0005 := @g_pm5_32 (.classMem (.cv x) A) ps ch
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) A) (syn_wb ps ch))
      (syn_wb (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv x) A) ch)) x p0005
  have p0007 :=
    @g_bitri (syn_wral x A (syn_wb ps ch))
      (.all x (.imp (.classMem (.cv x) A) (syn_wb ps ch)))
      (.all x (syn_wb (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv x) A) ch)))
      p0004 p0006
  have p0008 :=
    @g_n_3bitr4ri
      (.classEq (.cab x (syn_wa (.classMem (.cv x) A) ps))
        (.cab x (syn_wa (.classMem (.cv x) A) ch)))
      (.all x (syn_wb (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv x) A) ch)))
      (.classEq (syn_crab x A ps) (syn_crab x A ch)) (syn_wral x A (syn_wb ps ch)) p0000
      p0003 p0007
  exact p0008

@[expose]
noncomputable def g_raleqf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_raleq1f_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_raleq1f_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wral x A ph) (syn_wral x B ph))) :=
  by
  have p0000 := @g_nfeq x A B hyp_raleq1f_1 hyp_raleq1f_2
  have p0001 := @g_eleq2 A B (.cv x)
  have p0002 :=
    @g_imbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B) ph p0001
  have p0003 :=
    @g_albid (.classEq A B) (.imp (.classMem (.cv x) A) ph)
      (.imp (.classMem (.cv x) B) ph) x p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0005 := (Nominal.biimpRefl (syn_wral x B ph))
  have p0006 :=
    @g_n_3bitr4g (.classEq A B) (.all x (.imp (.classMem (.cv x) A) ph))
      (.all x (.imp (.classMem (.cv x) B) ph)) (syn_wral x A ph) (syn_wral x B ph) p0003
      p0004 p0005
  exact p0006

@[expose]
noncomputable def g_rexeqf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_raleq1f_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_raleq1f_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wrex x A ph) (syn_wrex x B ph))) :=
  by
  have p0000 := @g_nfeq x A B hyp_raleq1f_1 hyp_raleq1f_2
  have p0001 := @g_eleq2 A B (.cv x)
  have p0002 :=
    @g_anbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B) ph p0001
  have p0003 :=
    @g_exbid (.classEq A B) (syn_wa (.classMem (.cv x) A) ph)
      (syn_wa (.classMem (.cv x) B) ph) x p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0005 := (Nominal.biimpRefl (syn_wrex x B ph))
  have p0006 :=
    @g_n_3bitr4g (.classEq A B) (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wex x (syn_wa (.classMem (.cv x) B) ph)) (syn_wrex x A ph) (syn_wrex x B ph)
      p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_raleq (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wral x A ph) (syn_wral x B ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv x B
      (by
        first
        | (aesop))
  have p0002 := @g_raleqf ph x A B p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rexeq (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wrex x A ph) (syn_wrex x B ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv x B
      (by
        first
        | (aesop))
  have p0002 := @g_rexeqf ph x A B p0000 p0001
  exact p0002

@[expose]
noncomputable def g_raleqi (ph : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wral x A ph) (syn_wral x B ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_raleq ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := Nominal.mp hyp_raleq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_rexeqi (ph : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (syn_wrex x B ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rexeq ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := Nominal.mp hyp_raleq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_raleqdv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wral x A ps) (syn_wral x B ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_raleq ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wral x A ps) (syn_wral x B ps)) hyp_raleq1d_1
      p0000
  exact p0001

@[expose]
noncomputable def g_rexeqdv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wrex x A ps) (syn_wrex x B ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rexeq ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wrex x A ps) (syn_wrex x B ps)) hyp_raleq1d_1
      p0000
  exact p0001

@[expose]
noncomputable def g_raleqbi1dv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleqd_1 : Nominal.NPrf (.imp (.classEq A B) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wral x A ph) (syn_wral x B ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_raleq ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_ralbidv (.classEq A B) ph ps x B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_raleqd_1
  have p0002 :=
    @g_bitrd (.classEq A B) (syn_wral x A ph) (syn_wral x B ph) (syn_wral x B ps) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_rexeqbi1dv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleqd_1 : Nominal.NPrf (.imp (.classEq A B) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wrex x A ph) (syn_wrex x B ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rexeq ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_rexbidv (.classEq A B) ph ps x B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_raleqd_1
  have p0002 :=
    @g_bitrd (.classEq A B) (syn_wrex x A ph) (syn_wrex x B ph) (syn_wrex x B ps) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_raleqbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_raleqbidv_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_raleqbidv_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wral x A ps) (syn_wral x B ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_raleqdv ph ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_raleqbidv_1
  have p0001 :=
    @g_ralbidv ph ps ch x B
      (by
        first
        | (aesop))
      hyp_raleqbidv_2
  have p0002 :=
    @g_bitrd ph (syn_wral x A ps) (syn_wral x B ps) (syn_wral x B ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rexeqbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_raleqbidv_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_raleqbidv_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wrex x A ps) (syn_wrex x B ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rexeqdv ph ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_raleqbidv_1
  have p0001 :=
    @g_rexbidv ph ps ch x B
      (by
        first
        | (aesop))
      hyp_raleqbidv_2
  have p0002 :=
    @g_bitrd ph (syn_wrex x A ps) (syn_wrex x B ps) (syn_wrex x B ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_reu5 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wreu x A ph) (syn_wa (syn_wrex x A ph) (syn_wrmo x A ph))) :=
  by
  have p0000 := @g_eu5 (syn_wa (.classMem (.cv x) A) ph) x
  have p0001 := (Nominal.biimpRefl (syn_wreu x A ph))
  have p0002 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0003 := (Nominal.biimpRefl (syn_wrmo x A ph))
  have p0004 :=
    @g_anbi12i (syn_wrex x A ph) (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wrmo x A ph) (syn_wmo x (syn_wa (.classMem (.cv x) A) ph)) p0002 p0003
  have p0005 :=
    @g_n_3bitr4i (syn_weu x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
        (syn_wmo x (syn_wa (.classMem (.cv x) A) ph)))
      (syn_wreu x A ph) (syn_wa (syn_wrex x A ph) (syn_wrmo x A ph)) p0000 p0001 p0004
  exact p0005

@[expose]
noncomputable def g_cbvralf (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_cbvralf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_cbvralf_2 : Nominal.NPrf (syn_wnfc y A))
    (hyp_cbvralf_3 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvralf_4 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvralf_5 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wral x A ph) (syn_wral y A ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_nfv (.imp (.classMem (.cv x) A) ph) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 :=
    @g_nfcri x z A
      (by
        first
        | (aesop))
      hyp_cbvralf_1
  have p0002 :=
    @g_nfs1v ph x z
      (by
        first
        | (aesop))
  have p0003 := @g_nfim (.classMem (.cv z) A) (syn_wsb z x ph) x p0001 p0002
  have p0004 := @g_eleq1 (.cv x) (.cv z) A
  have p0005 := @g_sbequ12 ph x z
  have p0006_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb ph (syn_wsb z x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_imbi12d (.classEq (.cv x) (.cv z)) (.classMem (.cv x) A) (.classMem (.cv z) A) ph
      (syn_wsb z x ph) p0004 p0006_e01_recanon
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (syn_wb (.imp (.classMem (.cv x) A) ph)
          (.imp (.classMem (.cv z) A) (syn_wsb z x ph)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_cbval (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv z) A) (syn_wsb z x ph))
      x z p0000 p0003 p0007_e02_recanon
  have p0008 :=
    @g_nfcri y z A
      (by
        first
        | (aesop))
      hyp_cbvralf_2
  have p0009 :=
    @g_nfsb ph x z y
      (by
        first
        | (aesop))
      hyp_cbvralf_3
  have p0010 := @g_nfim (.classMem (.cv z) A) (syn_wsb z x ph) y p0008 p0009
  have p0011 :=
    @g_nfv (.imp (.classMem (.cv y) A) ps) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0012 := @g_eleq1 (.cv z) (.cv y) A
  have p0013 := @g_sbequ ph z y x
  have p0014 := @g_sbie ph ps x y hyp_cbvralf_4 hyp_cbvralf_5
  have p0015_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y)) (syn_wb (syn_wsb z x ph) (syn_wsb y x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0015 :=
    @g_syl6bb (.classEq (.cv z) (.cv y)) (syn_wsb z x ph) (syn_wsb y x ph) ps
      p0015_e00_recanon p0014
  have p0016 :=
    @g_imbi12d (.classEq (.cv z) (.cv y)) (.classMem (.cv z) A) (.classMem (.cv y) A)
      (syn_wsb z x ph) ps p0012 p0015
  have p0017_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (syn_wb (.imp (.classMem (.cv z) A) (syn_wsb z x ph))
          (.imp (.classMem (.cv y) A) ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @g_cbval (.imp (.classMem (.cv z) A) (syn_wsb z x ph)) (.imp (.classMem (.cv y) A) ps)
      z y p0010 p0011 p0017_e02_recanon
  have p0018 :=
    @g_bitri (.all x (.imp (.classMem (.cv x) A) ph))
      (.all z (.imp (.classMem (.cv z) A) (syn_wsb z x ph)))
      (.all y (.imp (.classMem (.cv y) A) ps)) p0007 p0017
  have p0019 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0020 := (Nominal.biimpRefl (syn_wral y A ps))
  have p0021 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) ph))
      (.all y (.imp (.classMem (.cv y) A) ps)) (syn_wral x A ph) (syn_wral y A ps) p0018
      p0019 p0020
  exact p0021

@[expose]
noncomputable def g_cbvrexf (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_cbvralf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_cbvralf_2 : Nominal.NPrf (syn_wnfc y A))
    (hyp_cbvralf_3 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvralf_4 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvralf_5 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (syn_wrex y A ps)) :=
  by
  have p0000 := @g_nfn ph y hyp_cbvralf_3
  have p0001 := @g_nfn ps x hyp_cbvralf_4
  have p0002_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_cbvralf_5
  have p0002 := @g_notbid (.classEq (.cv x) (.cv y)) ph ps p0002_e00_recanon
  have p0003_e04_recanon :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (.neg ph) (.neg ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @g_cbvralf (.neg ph) (.neg ps) x y A hyp_cbvralf_1 hyp_cbvralf_2 p0000 p0001
      p0003_e04_recanon
  have p0004 := @g_notbii (syn_wral x A (.neg ph)) (syn_wral y A (.neg ps)) p0003
  have p0005 := @g_dfrex2 ph x A
  have p0006 := @g_dfrex2 ps y A
  have p0007 :=
    @g_n_3bitr4i (.neg (syn_wral x A (.neg ph))) (.neg (syn_wral y A (.neg ps)))
      (syn_wrex x A ph) (syn_wrex y A ps) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_cbvral (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbvral_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvral_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvral_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wral x A ph) (syn_wral y A ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0002 := @g_cbvralf ph ps x y A p0000 p0001 hyp_cbvral_1 hyp_cbvral_2 hyp_cbvral_3
  exact p0002

@[expose]
noncomputable def g_cbvrex (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbvral_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvral_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvral_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (syn_wrex y A ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0002 := @g_cbvrexf ph ps x y A p0000 p0001 hyp_cbvral_1 hyp_cbvral_2 hyp_cbvral_3
  exact p0002

@[expose]
noncomputable def g_cbvralv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_cbvralv_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wral x A ph) (syn_wral y A ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 :=
    @g_cbvral ph ps x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001 hyp_cbvralv_1
  exact p0002

@[expose]
noncomputable def g_cbvrexv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_cbvralv_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (syn_wrex y A ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 :=
    @g_cbvrex ph ps x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001 hyp_cbvralv_1
  exact p0002

@[expose]
noncomputable def g_cbvral2v (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (w : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_w : w ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv)
    (dv_ch_w : w ∉ ch.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_z : z ∉ ph.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y) (dv_y_z : y ≠ z)
    (hyp_cbvral2v_1 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ph ch)))
    (hyp_cbvral2v_2 : Nominal.NPrf (.imp (.objEq y w) (syn_wb ch ps))) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B ph)) (syn_wral z A (syn_wral w B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ({ z } : Finset Var) ∪
          ({ w } : Finset Var) ∪
        A.fv ∪
      B.fv
  have p0000_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb ph ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_cbvral2v_1
  have p0000 :=
    @g_ralbidv (.classEq (.cv x) (.cv z)) ph ch y B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0000_e00_recanon
  have p0001_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (syn_wb (syn_wral y B ph) (syn_wral y B ch))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wral
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0001 :=
    @g_cbvralv (syn_wral y B ph) (syn_wral y B ch) x z A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      p0001_e00_recanon
  have p0002 :=
    @g_cbvralv ch ps y w B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_cbvral2v_2
  have p0003 := @g_ralbii (syn_wral y B ch) (syn_wral w B ps) z A p0002
  have p0004 :=
    @g_bitri (syn_wral x A (syn_wral y B ph)) (syn_wral z A (syn_wral y B ch))
      (syn_wral z A (syn_wral w B ps)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_cbvrexsv (ph : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf (syn_wb (syn_wrex x A ph) (syn_wrex y A (syn_wsb y x ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_nfv ph z
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfs1v ph x z
      (by
        first
        | (aesop))
  have p0002 := @g_sbequ12 ph x z
  have p0003 :=
    @g_cbvrex ph (syn_wsb z x ph) x z A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001 p0002
  have p0004 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0005 :=
    @g_nfsb ph x z y
      (by
        first
        | (aesop))
      p0004
  have p0006 :=
    @g_nfv (syn_wsb y x ph) z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb,
              Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
  have p0007 := @g_sbequ ph z y x
  have p0008 :=
    @g_cbvrex (syn_wsb z x ph) (syn_wsb y x ph) z y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0005 p0006 p0007
  have p0009 :=
    @g_bitri (syn_wrex x A ph) (syn_wrex z A (syn_wsb z x ph))
      (syn_wrex y A (syn_wsb y x ph)) p0003 p0008
  exact p0009

@[expose]
noncomputable def g_rabbidva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_rabbidva_1 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_crab x A ps) (syn_crab x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_ralrimiva ph (syn_wb ps ch) x A
      (by
        first
        | (aesop))
      hyp_rabbidva_1
  have p0001 := @g_rabbi ps ch x A
  have p0002 :=
    @g_sylib ph (syn_wral x A (syn_wb ps ch))
      (.classEq (syn_crab x A ps) (syn_crab x A ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rabbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_rabbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_crab x A ps) (syn_crab x A ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_adantr ph (syn_wb ps ch) (.classMem (.cv x) A) hyp_rabbidv_1
  have p0001 :=
    @g_rabbidva ph ps ch x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_rabeqf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_rabeqf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_rabeqf_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_crab x A ph) (syn_crab x B ph))) :=
  by
  have p0000 := @g_nfeq x A B hyp_rabeqf_1 hyp_rabeqf_2
  have p0001 := @g_eleq2 A B (.cv x)
  have p0002 :=
    @g_anbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B) ph p0001
  have p0003 :=
    @g_abbid (.classEq A B) (syn_wa (.classMem (.cv x) A) ph)
      (syn_wa (.classMem (.cv x) B) ph) x p0000 p0002
  have p0004 := (Nominal.classEqRefl (syn_crab x A ph))
  have p0005 := (Nominal.classEqRefl (syn_crab x B ph))
  have p0006 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wa (.classMem (.cv x) A) ph))
      (.cab x (syn_wa (.classMem (.cv x) B) ph)) (syn_crab x A ph) (syn_crab x B ph) p0003
      p0004 p0005
  exact p0006

@[expose]
noncomputable def g_rabeq (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_crab x A ph) (syn_crab x B ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv x B
      (by
        first
        | (aesop))
  have p0002 := @g_rabeqf ph x A B p0000 p0001
  exact p0002

@[expose]
noncomputable def g_vex (x : Var) : Nominal.NPrf (.classMem (.cv x) (syn_cvv)) :=
  by
  have p0000 := @g_eqid (.cv x)
  have p0001 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_v x
  have p0002_e00_recanon :
    Nominal.NPrf (.classEq (syn_cvv) (.cab x (.classEq (.cv x) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0001
  have p0002 := @g_eqabri (.classEq (.cv x) (.cv x)) x (syn_cvv) p0002_e00_recanon
  have p0003 :=
    @g_mpbir (.classMem (.cv x) (syn_cvv)) (.classEq (.cv x) (.cv x)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_isset (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cvv)) (syn_wex x (.classEq (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A
      (syn_cvv) (by
        first
        | (aesop)) (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop)))
  have p0001 := @g_vex x
  have p0002 := @g_biantru (.classMem (.cv x) (syn_cvv)) (.classEq (.cv x) A) p0001
  have p0003 :=
    @g_exbii (.classEq (.cv x) A)
      (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) (syn_cvv))) x p0002
  have p0004 :=
    @g_bitr4i (.classMem A (syn_cvv))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) (syn_cvv))))
      (syn_wex x (.classEq (.cv x) A)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_issetf (x : Var) (A : Class)
    (hyp_issetf_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cvv)) (syn_wex x (.classEq (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_isset y A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfeq2 x (.cv y) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      hyp_issetf_1
  have p0002 :=
    @g_nfv (.classEq (.cv x) A) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 := @g_eqeq1 (.cv y) (.cv x) A
  have p0004_e02_recanon :
    Nominal.NPrf (.imp (.objEq y x) (syn_wb (.classEq (.cv y) A) (.classEq (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @g_cbvex (.classEq (.cv y) A) (.classEq (.cv x) A) y x p0001 p0002 p0004_e02_recanon
  have p0005 :=
    @g_bitri (.classMem A (syn_cvv)) (syn_wex y (.classEq (.cv y) A))
      (syn_wex x (.classEq (.cv x) A)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_isseti (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_isseti_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wex x (.classEq (.cv x) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_isset x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mpbi (.classMem A (syn_cvv)) (syn_wex x (.classEq (.cv x) A)) hyp_isseti_1 p0000
  exact p0001

@[expose]
noncomputable def g_elex (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem A (syn_cvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
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
  have p0000 := @g_exsimpl (.classEq (.cv x) A) (.classMem (.cv x) B) x
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A B (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0002 :=
    @g_isset x A
      (by
        first
        | (aesop))
  have p0003 :=
    @g_n_3imtr4i (syn_wex x (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) B)))
      (syn_wex x (.classEq (.cv x) A)) (.classMem A B) (.classMem A (syn_cvv)) p0000 p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_elexi (A : Class) (B : Class)
    (hyp_elisseti_1 : Nominal.NPrf (.classMem A B)) :
    Nominal.NPrf (.classMem A (syn_cvv)) :=
  by
  have p0000 := @g_elex A B
  have p0001 := Nominal.mp hyp_elisseti_1 p0000
  exact p0001

@[expose]
noncomputable def g_elisset (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wex x (.classEq (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := @g_elex A V
  have p0001 :=
    @g_isset x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sylib (.classMem A V) (.classMem A (syn_cvv)) (syn_wex x (.classEq (.cv x) A))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ralv (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wral x (syn_cvv) ph) (.all x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wral x (syn_cvv) ph))
  have p0001 := @g_vex x
  have p0002 := @g_a1bi (.classMem (.cv x) (syn_cvv)) ph p0001
  have p0003 := @g_albii ph (.imp (.classMem (.cv x) (syn_cvv)) ph) x p0002
  have p0004 :=
    @g_bitr4i (syn_wral x (syn_cvv) ph) (.all x (.imp (.classMem (.cv x) (syn_cvv)) ph))
      (.all x ph) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_rexv (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wrex x (syn_cvv) ph) (syn_wex x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wrex x (syn_cvv) ph))
  have p0001 := @g_vex x
  have p0002 := @g_biantrur (.classMem (.cv x) (syn_cvv)) ph p0001
  have p0003 := @g_exbii ph (syn_wa (.classMem (.cv x) (syn_cvv)) ph) x p0002
  have p0004 :=
    @g_bitr4i (syn_wrex x (syn_cvv) ph)
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_cvv)) ph)) (syn_wex x ph) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_rabab (ph : Wff) (x : Var) :
    Nominal.NPrf (.classEq (syn_crab x (syn_cvv) ph) (.cab x ph)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_crab x (syn_cvv) ph))
  have p0001 := @g_vex x
  have p0002 := @g_biantrur (.classMem (.cv x) (syn_cvv)) ph p0001
  have p0003 := @g_abbii ph (syn_wa (.classMem (.cv x) (syn_cvv)) ph) x p0002
  have p0004 :=
    @g_eqtr4i (syn_crab x (syn_cvv) ph) (.cab x (syn_wa (.classMem (.cv x) (syn_cvv)) ph))
      (.cab x ph) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_ralcom4 (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wral x A (.all y ph)) (.all y (syn_wral x A ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_ralcom ph x y A (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_ralv ph y
  have p0002 := @g_ralbii (syn_wral y (syn_cvv) ph) (.all y ph) x A p0001
  have p0003 := @g_ralv (syn_wral x A ph) y
  have p0004 :=
    @g_n_3bitr3i (syn_wral x A (syn_wral y (syn_cvv) ph))
      (syn_wral y (syn_cvv) (syn_wral x A ph)) (syn_wral x A (.all y ph))
      (.all y (syn_wral x A ph)) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_rexcom4 (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wrex x A (syn_wex y ph)) (syn_wex y (syn_wrex x A ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_rexcom ph x y A (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_rexv ph y
  have p0002 := @g_rexbii (syn_wrex y (syn_cvv) ph) (syn_wex y ph) x A p0001
  have p0003 := @g_rexv (syn_wrex x A ph) y
  have p0004 :=
    @g_n_3bitr3i (syn_wrex x A (syn_wrex y (syn_cvv) ph))
      (syn_wrex y (syn_cvv) (syn_wrex x A ph)) (syn_wrex x A (syn_wex y ph))
      (syn_wex y (syn_wrex x A ph)) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_ceqsalg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (hyp_ceqsalg_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_ceqsalg_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.all x (.imp (.classEq (.cv x) A) ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_elisset x A V
      (by
        first
        | (aesop))
  have p0001 := @g_nfa1 (.imp (.classEq (.cv x) A) ph) x
  have p0002 := @g_biimpd (.classEq (.cv x) A) ph ps hyp_ceqsalg_2
  have p0003 := @g_a2i (.classEq (.cv x) A) ph ps p0002
  have p0004 :=
    @g_sps (.imp (.classEq (.cv x) A) ph) (.imp (.classEq (.cv x) A) ps) x p0003
  have p0005 :=
    @g_exlimd (.all x (.imp (.classEq (.cv x) A) ph)) (.classEq (.cv x) A) ps x p0001
      hyp_ceqsalg_1 p0004
  have p0006 :=
    @g_syl5com (.classMem A V) (syn_wex x (.classEq (.cv x) A))
      (.all x (.imp (.classEq (.cv x) A) ph)) ps p0000 p0005
  have p0007 := @g_biimprcd (.classEq (.cv x) A) ph ps hyp_ceqsalg_2
  have p0008 := @g_alrimi ps (.imp (.classEq (.cv x) A) ph) x hyp_ceqsalg_1 p0007
  have p0009 :=
    @g_impbid1 (.classMem A V) (.all x (.imp (.classEq (.cv x) A) ph)) ps p0006 p0008
  exact p0009

@[expose]
noncomputable def g_ceqsal (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_ceqsal_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_ceqsal_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ceqsal_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.all x (.imp (.classEq (.cv x) A) ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_ceqsalg ph ps x A (syn_cvv)
      (by
        first
        | (aesop))
      hyp_ceqsal_1 hyp_ceqsal_3
  have p0001 := Nominal.mp hyp_ceqsal_2 p0000
  exact p0001

@[expose]
noncomputable def g_ceqsalv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsalv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ceqsalv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.all x (.imp (.classEq (.cv x) A) ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_ceqsal ph ps x A
      (by
        first
        | (aesop))
      p0000 hyp_ceqsalv_1 hyp_ceqsalv_2
  exact p0001

@[expose]
noncomputable def g_ceqsex (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_ceqsex_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_ceqsex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ceqsex_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_biimpa (.classEq (.cv x) A) ph ps hyp_ceqsex_3
  have p0001 := @g_exlimi (syn_wa (.classEq (.cv x) A) ph) ps x hyp_ceqsex_1 p0000
  have p0002 := @g_biimprcd (.classEq (.cv x) A) ph ps hyp_ceqsex_3
  have p0003 := @g_alrimi ps (.imp (.classEq (.cv x) A) ph) x hyp_ceqsex_1 p0002
  have p0004 :=
    @g_isseti x A
      (by
        first
        | (aesop))
      hyp_ceqsex_2
  have p0005 := @g_exintr (.classEq (.cv x) A) ph x
  have p0006 :=
    @g_ee10 ps (.all x (.imp (.classEq (.cv x) A) ph)) (syn_wex x (.classEq (.cv x) A))
      (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) p0003 p0004 p0005
  have p0007 := @g_impbii (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps p0001 p0006
  exact p0007

@[expose]
noncomputable def g_ceqsexv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsexv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ceqsexv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_ceqsex ph ps x A
      (by
        first
        | (aesop))
      p0000 hyp_ceqsexv_1 hyp_ceqsexv_2
  exact p0001

@[expose]
noncomputable def g_ceqsex2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_ceqsex2_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_ceqsex2_2 : Nominal.NPrf (syn_wnf y ch))
    (hyp_ceqsex2_3 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ceqsex2_4 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_ceqsex2_5 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_ceqsex2_6 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch))) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph)))
        ch) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_n_3anass (.classEq (.cv x) A) (.classEq (.cv y) B) ph
  have p0001 :=
    @g_exbii (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph)
      (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph)) y p0000
  have p0002 :=
    @g_n_19_42v (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_bitri (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph))
      (syn_wex y (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph)))
      (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) B) ph))) p0001
      p0002
  have p0004 :=
    @g_exbii (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph))
      (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) B) ph))) x p0003
  have p0005 :=
    @g_nfv (.classEq (.cv y) B) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 := @g_nfan (.classEq (.cv y) B) ps x p0005 hyp_ceqsex2_1
  have p0007 := @g_nfex (syn_wa (.classEq (.cv y) B) ps) x y p0006
  have p0008 := @g_anbi2d (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) hyp_ceqsex2_5
  have p0009 :=
    @g_exbidv (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph)
      (syn_wa (.classEq (.cv y) B) ps) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0008
  have p0010 :=
    @g_ceqsex (syn_wex y (syn_wa (.classEq (.cv y) B) ph))
      (syn_wex y (syn_wa (.classEq (.cv y) B) ps)) x A
      (by
        first
        | (aesop))
      p0007 hyp_ceqsex2_3 p0009
  have p0011 :=
    @g_ceqsex ps ch y B
      (by
        first
        | (aesop))
      hyp_ceqsex2_2 hyp_ceqsex2_4 hyp_ceqsex2_6
  have p0012 :=
    @g_n_3bitri
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph)))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) B) ph))))
      (syn_wex y (syn_wa (.classEq (.cv y) B) ps)) ch p0004 p0010 p0011
  exact p0012

@[expose]
noncomputable def g_ceqsex2v (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ch_y : y ∉ ch.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ceqsex2v_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ceqsex2v_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_ceqsex2v_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_ceqsex2v_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch))) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph)))
        ch) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ch y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_ceqsex2 ph ps ch x y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001 hyp_ceqsex2v_1 hyp_ceqsex2v_2 hyp_ceqsex2v_3 hyp_ceqsex2v_4
  exact p0002

@[expose]
noncomputable def g_vtoclgft (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (syn_wnfc x A) (syn_wnf x ps))
          (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
          (.classMem A V)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 := @g_elex A V
  have p0001 :=
    @g_elisset z A (syn_cvv)
      (by
        first
        | (aesop))
  have p0002 :=
    @g_n_3ad2ant3 (.classMem A (syn_cvv)) (syn_wa (syn_wnfc x A) (syn_wnf x ps))
      (syn_wex z (.classEq (.cv z) A))
      (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph)) p0001
  have p0003 := @g_nfnfc1 x A
  have p0004 :=
    @g_nfcvd (syn_wnfc x A) x (.cv z)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @g_id (syn_wnfc x A)
  have p0006 := @g_nfeqd (syn_wnfc x A) x (.cv z) A p0004 p0005
  have p0007 := @g_eqeq1 (.cv z) (.cv x) A
  have p0008 :=
    @g_a1i
      (.imp (.classEq (.cv z) (.cv x)) (syn_wb (.classEq (.cv z) A) (.classEq (.cv x) A)))
      (syn_wnfc x A) p0007
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wnfc x A)
        (.imp (.objEq z x) (syn_wb (.classEq (.cv z) A) (.classEq (.cv x) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wnfc syn_wnf syn_wb
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @g_cbvexd (syn_wnfc x A) (.classEq (.cv z) A) (.classEq (.cv x) A) z x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wnfc,
              Finset.mem_erase] at ⊢;
            aesop))
      p0003 p0006 p0009_e02_recanon
  have p0010 :=
    @g_ad2antrr (syn_wnfc x A)
      (syn_wb (syn_wex z (.classEq (.cv z) A)) (syn_wex x (.classEq (.cv x) A)))
      (syn_wnf x ps)
      (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph)) p0009
  have p0011 :=
    @g_n_3adant3 (syn_wa (syn_wnfc x A) (syn_wnf x ps))
      (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
      (syn_wb (syn_wex z (.classEq (.cv z) A)) (syn_wex x (.classEq (.cv x) A)))
      (.classMem A (syn_cvv)) p0010
  have p0012 :=
    @g_mpbid
      (syn_w3a (syn_wa (syn_wnfc x A) (syn_wnf x ps))
        (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
        (.classMem A (syn_cvv)))
      (syn_wex z (.classEq (.cv z) A)) (syn_wex x (.classEq (.cv x) A)) p0002 p0011
  have p0013 := @g_bi1 ph ps
  have p0014 := @g_imim2i (syn_wb ph ps) (.imp ph ps) (.classEq (.cv x) A) p0013
  have p0015 :=
    @g_com23 (.imp (.classEq (.cv x) A) (syn_wb ph ps)) (.classEq (.cv x) A) ph ps p0014
  have p0016 :=
    @g_imp (.imp (.classEq (.cv x) A) (syn_wb ph ps)) ph (.imp (.classEq (.cv x) A) ps)
      p0015
  have p0017 :=
    @g_alanimi (.imp (.classEq (.cv x) A) (syn_wb ph ps)) ph
      (.imp (.classEq (.cv x) A) ps) x p0016
  have p0018 :=
    @g_n_3ad2ant2 (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
      (syn_wa (syn_wnfc x A) (syn_wnf x ps)) (.all x (.imp (.classEq (.cv x) A) ps))
      (.classMem A (syn_cvv)) p0017
  have p0019 :=
    @g_simp1r (syn_wnfc x A) (syn_wnf x ps)
      (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
      (.classMem A (syn_cvv))
  have p0020 := @g_n_19_23t (.classEq (.cv x) A) ps x
  have p0021 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wnfc x A) (syn_wnf x ps))
        (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
        (.classMem A (syn_cvv)))
      (syn_wnf x ps)
      (syn_wb (.all x (.imp (.classEq (.cv x) A) ps))
        (.imp (syn_wex x (.classEq (.cv x) A)) ps))
      p0019 p0020
  have p0022 :=
    @g_mpbid
      (syn_w3a (syn_wa (syn_wnfc x A) (syn_wnf x ps))
        (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
        (.classMem A (syn_cvv)))
      (.all x (.imp (.classEq (.cv x) A) ps)) (.imp (syn_wex x (.classEq (.cv x) A)) ps)
      p0018 p0021
  have p0023 :=
    @g_mpd
      (syn_w3a (syn_wa (syn_wnfc x A) (syn_wnf x ps))
        (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
        (.classMem A (syn_cvv)))
      (syn_wex x (.classEq (.cv x) A)) ps p0012 p0022
  have p0024 :=
    @g_syl3an3 (.classMem A V) (syn_wa (syn_wnfc x A) (syn_wnf x ps))
      (syn_wa (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (.all x ph))
      (.classMem A (syn_cvv)) ps p0000 p0023
  exact p0024

@[expose]
noncomputable def g_vtocldf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (V : Class) (hyp_vtocld_1 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_vtocld_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (syn_wb ps ch)))
    (hyp_vtocld_3 : Nominal.NPrf (.imp ph ps))
    (hyp_vtocldf_4 : Nominal.NPrf (syn_wnf x ph))
    (hyp_vtocldf_5 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_vtocldf_6 : Nominal.NPrf (.imp ph (syn_wnf x ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_ex ph (.classEq (.cv x) A) (syn_wb ps ch) hyp_vtocld_2
  have p0001 :=
    @g_alrimi ph (.imp (.classEq (.cv x) A) (syn_wb ps ch)) x hyp_vtocldf_4 p0000
  have p0002 := @g_alrimi ph ps x hyp_vtocldf_4 hyp_vtocld_3
  have p0003 := @g_vtoclgft ps ch x A V
  have p0004 :=
    @g_syl221anc ph (syn_wnfc x A) (syn_wnf x ch)
      (.all x (.imp (.classEq (.cv x) A) (syn_wb ps ch))) (.all x ps) (.classMem A V) ch
      hyp_vtocldf_5 hyp_vtocldf_6 p0001 p0002 hyp_vtocld_1 p0003
  exact p0004

@[expose]
noncomputable def g_vtocld (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (V : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_vtocld_1 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_vtocld_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (syn_wb ps ch)))
    (hyp_vtocld_3 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph ch) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcvd ph x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfvd ph ch x
      (by
        first
        | (aesop))
  have p0003 :=
    @g_vtocldf ph ps ch x A V hyp_vtocld_1 hyp_vtocld_2 hyp_vtocld_3 p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_vtoclf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_vtoclf_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_vtoclf_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_vtoclf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtoclf_4 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_isseti x A
      (by
        first
        | (aesop))
      hyp_vtoclf_2
  have p0001 := @g_biimpd (.classEq (.cv x) A) ph ps hyp_vtoclf_3
  have p0002 := @g_eximi (.classEq (.cv x) A) (.imp ph ps) x p0001
  have p0003 := Nominal.mp p0000 p0002
  have p0004 := @g_n_19_36i ph ps x hyp_vtoclf_1 p0003
  have p0005 := @g_mpg ph ps x p0004 hyp_vtoclf_4
  exact p0005

@[expose]
noncomputable def g_vtocl (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_vtocl_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_vtocl_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtocl_3 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_vtoclf ph ps x A
      (by
        first
        | (aesop))
      p0000 hyp_vtocl_1 hyp_vtocl_2 hyp_vtocl_3
  exact p0001

@[expose]
noncomputable def g_vtocl2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_vtocl2_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_vtocl2_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_vtocl2_3 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps)))
    (hyp_vtocl2_4 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_isseti x A
      (by
        first
        | (aesop))
      hyp_vtocl2_1
  have p0001 :=
    @g_isseti y B
      (by
        first
        | (aesop))
      hyp_vtocl2_2
  have p0002 :=
    @g_eeanv (.classEq (.cv x) A) (.classEq (.cv y) B) x y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_biimpd (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph ps hyp_vtocl2_3
  have p0004 :=
    @g_n_2eximi (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.imp ph ps) x y p0003
  have p0005 :=
    @g_sylbir (syn_wa (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))))
      (syn_wex x (syn_wex y (.imp ph ps))) p0002 p0004
  have p0006 :=
    @g_mp2an (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B))
      (syn_wex x (syn_wex y (.imp ph ps))) p0000 p0001 p0005
  have p0007 :=
    @g_n_19_36v ph ps y
      (by
        first
        | (aesop))
  have p0008 := @g_exbii (syn_wex y (.imp ph ps)) (.imp (.all y ph) ps) x p0007
  have p0009 :=
    @g_mpbi (syn_wex x (syn_wex y (.imp ph ps))) (syn_wex x (.imp (.all y ph) ps)) p0006
      p0008
  have p0010 :=
    @g_n_19_36aiv (.all y ph) ps x
      (by
        first
        | (aesop))
      p0009
  have p0011 := Nominal.gen hyp_vtocl2_4 y
  have p0012 := @g_mpg (.all y ph) ps x p0010 p0011
  exact p0012

@[expose]
noncomputable def g_vtoclb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var)
    (A : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_th_x : x ∉ th.fv)
    (hyp_vtoclb_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_vtoclb_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ch)))
    (hyp_vtoclb_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ps th)))
    (hyp_vtoclb_4 : Nominal.NPrf (syn_wb ph ps)) : Nominal.NPrf (syn_wb ch th) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_bibi12d (.classEq (.cv x) A) ph ch ps th hyp_vtoclb_2 hyp_vtoclb_3
  have p0001 :=
    @g_vtocl (syn_wb ph ps) (syn_wb ch th) x A
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_vtoclb_1 p0000 hyp_vtoclb_4
  exact p0001

@[expose]
noncomputable def g_vtoclgf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (hyp_vtoclgf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_vtoclgf_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_vtoclgf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtoclgf_4 : Nominal.NPrf ph) : Nominal.NPrf (.imp (.classMem A V) ps) :=
  by
  have p0000 := @g_elex A V
  have p0001 := @g_issetf x A hyp_vtoclgf_1
  have p0002 := @g_mpbii (.classEq (.cv x) A) ph ps hyp_vtoclgf_4 hyp_vtoclgf_3
  have p0003 := @g_exlimi (.classEq (.cv x) A) ps x hyp_vtoclgf_2 p0002
  have p0004 :=
    @g_sylbi (.classMem A (syn_cvv)) (syn_wex x (.classEq (.cv x) A)) ps p0001 p0003
  have p0005 := @g_syl (.classMem A V) (.classMem A (syn_cvv)) ps p0000 p0004
  exact p0005

@[expose]
noncomputable def g_vtoclg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_vtoclg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtoclg_2 : Nominal.NPrf ph) : Nominal.NPrf (.imp (.classMem A V) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 := @g_vtoclgf ph ps x A V p0000 p0001 hyp_vtoclg_1 hyp_vtoclg_2
  exact p0002

@[expose]
noncomputable def g_vtoclbg (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var)
    (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_th_x : x ∉ th.fv)
    (hyp_vtoclbg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ch)))
    (hyp_vtoclbg_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ps th)))
    (hyp_vtoclbg_3 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb ch th)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := @g_bibi12d (.classEq (.cv x) A) ph ch ps th hyp_vtoclbg_1 hyp_vtoclbg_2
  have p0001 :=
    @g_vtoclg (syn_wb ph ps) (syn_wb ch th) x A V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 hyp_vtoclbg_3
  exact p0001

@[expose]
noncomputable def g_vtocl2gf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (V : Class) (W : Class)
    (hyp_vtocl2gf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_vtocl2gf_2 : Nominal.NPrf (syn_wnfc y A))
    (hyp_vtocl2gf_3 : Nominal.NPrf (syn_wnfc y B))
    (hyp_vtocl2gf_4 : Nominal.NPrf (syn_wnf x ps))
    (hyp_vtocl2gf_5 : Nominal.NPrf (syn_wnf y ch))
    (hyp_vtocl2gf_6 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtocl2gf_7 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch)))
    (hyp_vtocl2gf_8 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) ch) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        V.fv ∪
      W.fv
  have p0000 := @g_elex A V
  have p0001 :=
    @g_nfel1 y A (syn_cvv)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      hyp_vtocl2gf_2
  have p0002 := @g_nfim (.classMem A (syn_cvv)) ch y p0001 hyp_vtocl2gf_5
  have p0003 :=
    @g_imbi2d (.classEq (.cv y) B) ps ch (.classMem A (syn_cvv)) hyp_vtocl2gf_7
  have p0004 :=
    @g_vtoclgf ph ps x A (syn_cvv) hyp_vtocl2gf_1 hyp_vtocl2gf_4 hyp_vtocl2gf_6
      hyp_vtocl2gf_8
  have p0005 :=
    @g_vtoclgf (.imp (.classMem A (syn_cvv)) ps) (.imp (.classMem A (syn_cvv)) ch) y B W
      hyp_vtocl2gf_3 p0002 p0003 p0004
  have p0006 :=
    @g_mpan9 (.classMem A V) (.classMem A (syn_cvv)) (.classMem B W) ch p0000 p0005
  exact p0006

@[expose]
noncomputable def g_vtocl2g (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_ch_y : y ∉ ch.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_vtocl2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtocl2g_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch)))
    (hyp_vtocl2g_3 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) ch) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        V.fv ∪
      W.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfcv y B
      (by
        first
        | (aesop))
  have p0003 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0004 :=
    @g_nfv ch y
      (by
        first
        | (aesop))
  have p0005 :=
    @g_vtocl2gf ph ps ch x y A B V W p0000 p0001 p0002 p0003 p0004 hyp_vtocl2g_1
      hyp_vtocl2g_2 hyp_vtocl2g_3
  exact p0005

@[expose]
noncomputable def g_vtoclgaf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) (hyp_vtoclgaf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_vtoclgaf_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_vtoclgaf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtoclgaf_4 : Nominal.NPrf (.imp (.classMem (.cv x) B) ph)) :
    Nominal.NPrf (.imp (.classMem A B) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfel1 x A B
      (by
        first
        | (aesop))
      hyp_vtoclgaf_1
  have p0001 := @g_nfim (.classMem A B) ps x p0000 hyp_vtoclgaf_2
  have p0002 := @g_eleq1 (.cv x) A B
  have p0003 :=
    @g_imbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0002
      hyp_vtoclgaf_3
  have p0004 :=
    @g_vtoclgf (.imp (.classMem (.cv x) B) ph) (.imp (.classMem A B) ps) x A B
      hyp_vtoclgaf_1 p0001 p0003 hyp_vtoclgaf_4
  have p0005 := @g_pm2_43i (.classMem A B) ps p0004
  exact p0005

@[expose]
noncomputable def g_vtoclga (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_vtoclga_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtoclga_2 : Nominal.NPrf (.imp (.classMem (.cv x) B) ph)) :
    Nominal.NPrf (.imp (.classMem A B) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 :=
    @g_vtoclgaf ph ps x A B
      (by
        first
        | (aesop))
      p0000 p0001 hyp_vtoclga_1 hyp_vtoclga_2
  exact p0002

@[expose]
noncomputable def g_vtocl2gaf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y)
    (hyp_vtocl2gaf_a : Nominal.NPrf (syn_wnfc x A))
    (hyp_vtocl2gaf_b : Nominal.NPrf (syn_wnfc y A))
    (hyp_vtocl2gaf_c : Nominal.NPrf (syn_wnfc y B))
    (hyp_vtocl2gaf_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_vtocl2gaf_2 : Nominal.NPrf (syn_wnf y ch))
    (hyp_vtocl2gaf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtocl2gaf_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch)))
    (hyp_vtocl2gaf_5 :
      Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)) ph)) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B D)) ch) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @g_nfel1 x A C
      (by
        first
        | (aesop))
      hyp_vtocl2gaf_a
  have p0001 :=
    @g_nfv (.classMem (.cv y) D) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @g_nfan (.classMem A C) (.classMem (.cv y) D) x p0000 p0001
  have p0003 :=
    @g_nfim (syn_wa (.classMem A C) (.classMem (.cv y) D)) ps x p0002 hyp_vtocl2gaf_1
  have p0004 :=
    @g_nfel1 y A C
      (by
        first
        | (aesop))
      hyp_vtocl2gaf_b
  have p0005 :=
    @g_nfel1 y B D
      (by
        first
        | (aesop))
      hyp_vtocl2gaf_c
  have p0006 := @g_nfan (.classMem A C) (.classMem B D) y p0004 p0005
  have p0007 :=
    @g_nfim (syn_wa (.classMem A C) (.classMem B D)) ch y p0006 hyp_vtocl2gaf_2
  have p0008 := @g_eleq1 (.cv x) A C
  have p0009 :=
    @g_anbi1d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C)
      (.classMem (.cv y) D) p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv x) A) (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))
      (syn_wa (.classMem A C) (.classMem (.cv y) D)) ph ps p0009 hyp_vtocl2gaf_3
  have p0011 := @g_eleq1 (.cv y) B D
  have p0012 :=
    @g_anbi2d (.classEq (.cv y) B) (.classMem (.cv y) D) (.classMem B D) (.classMem A C)
      p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv y) B) (syn_wa (.classMem A C) (.classMem (.cv y) D))
      (syn_wa (.classMem A C) (.classMem B D)) ps ch p0012 hyp_vtocl2gaf_4
  have p0014 :=
    @g_vtocl2gf (.imp (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)) ph)
      (.imp (syn_wa (.classMem A C) (.classMem (.cv y) D)) ps)
      (.imp (syn_wa (.classMem A C) (.classMem B D)) ch) x y A B C D hyp_vtocl2gaf_a
      hyp_vtocl2gaf_b hyp_vtocl2gaf_c p0003 p0007 p0010 p0013 hyp_vtocl2gaf_5
  have p0015 := @g_pm2_43i (syn_wa (.classMem A C) (.classMem B D)) ch p0014
  exact p0015

@[expose]
noncomputable def g_vtocl2ga (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_ch_y : y ∉ ch.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_vtocl2ga_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_vtocl2ga_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch)))
    (hyp_vtocl2ga_3 :
      Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)) ph)) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B D)) ch) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfcv y B
      (by
        first
        | (aesop))
  have p0003 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0004 :=
    @g_nfv ch y
      (by
        first
        | (aesop))
  have p0005 :=
    @g_vtocl2gaf ph ps ch x y A B C D
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001 p0002 p0003 p0004 hyp_vtocl2ga_1 hyp_vtocl2ga_2 hyp_vtocl2ga_3
  exact p0005

@[expose]
noncomputable def g_vtocleg (ph : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_vtocleg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) ph)) :
    Nominal.NPrf (.imp (.classMem A V) ph) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_elisset x A V
      (by
        first
        | (aesop))
  have p0001 :=
    @g_exlimiv (.classEq (.cv x) A) ph x
      (by
        first
        | (aesop))
      hyp_vtocleg_1
  have p0002 := @g_syl (.classMem A V) (syn_wex x (.classEq (.cv x) A)) ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_spcimgft (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_spcimgft_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_spcimgft_2 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf
      (.imp (.all x (.imp (.classEq (.cv x) A) (.imp ph ps)))
        (.imp (.classMem A B) (.imp (.all x ph) ps))) :=
  by
  have p0000 := @g_elex A B
  have p0001 := @g_issetf x A hyp_spcimgft_2
  have p0002 := @g_exim (.classEq (.cv x) A) (.imp ph ps) x
  have p0003 :=
    @g_syl5bi (.classMem A (syn_cvv)) (syn_wex x (.classEq (.cv x) A))
      (.all x (.imp (.classEq (.cv x) A) (.imp ph ps))) (syn_wex x (.imp ph ps)) p0001
      p0002
  have p0004 := @g_n_19_36 ph ps x hyp_spcimgft_1
  have p0005 :=
    @g_syl6ib (.all x (.imp (.classEq (.cv x) A) (.imp ph ps))) (.classMem A (syn_cvv))
      (syn_wex x (.imp ph ps)) (.imp (.all x ph) ps) p0003 p0004
  have p0006 :=
    @g_syl5 (.classMem A B) (.classMem A (syn_cvv))
      (.all x (.imp (.classEq (.cv x) A) (.imp ph ps))) (.imp (.all x ph) ps) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_spcgft (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_spcimgft_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_spcimgft_2 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf
      (.imp (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
        (.imp (.classMem A B) (.imp (.all x ph) ps))) :=
  by
  have p0000 := @g_bi1 ph ps
  have p0001 := @g_imim2i (syn_wb ph ps) (.imp ph ps) (.classEq (.cv x) A) p0000
  have p0002 :=
    @g_alimi (.imp (.classEq (.cv x) A) (syn_wb ph ps))
      (.imp (.classEq (.cv x) A) (.imp ph ps)) x p0001
  have p0003 := @g_spcimgft ph ps x A B hyp_spcimgft_1 hyp_spcimgft_2
  have p0004 :=
    @g_syl (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
      (.all x (.imp (.classEq (.cv x) A) (.imp ph ps)))
      (.imp (.classMem A B) (.imp (.all x ph) ps)) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_spcgf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (hyp_spcgf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_spcgf_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_spcgf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (.imp (.all x ph) ps)) :=
  by
  have p0000 := @g_spcgft ph ps x A V hyp_spcgf_2 hyp_spcgf_1
  have p0001 :=
    @g_mpg (.imp (.classEq (.cv x) A) (syn_wb ph ps))
      (.imp (.classMem A V) (.imp (.all x ph) ps)) x p0000 hyp_spcgf_3
  exact p0001

@[expose]
noncomputable def g_spcegf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (hyp_spcgf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_spcgf_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_spcgf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (.imp ps (syn_wex x ph))) :=
  by
  have p0000 := @g_nfn ps x hyp_spcgf_2
  have p0001 := @g_notbid (.classEq (.cv x) A) ph ps hyp_spcgf_3
  have p0002 := @g_spcgf (.neg ph) (.neg ps) x A V hyp_spcgf_1 p0000 p0001
  have p0003 := @g_con2d (.classMem A V) (.all x (.neg ph)) ps p0002
  have p0004 := (Nominal.biimpRefl (syn_wex x ph))
  have p0005 :=
    @g_syl6ibr (.classMem A V) ps (.neg (.all x (.neg ph))) (syn_wex x ph) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_spcimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_spcimdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_spcimdv_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_ex ph (.classEq (.cv x) A) (.imp ps ch) hyp_spcimdv_2
  have p0001 :=
    @g_alrimiv ph (.imp (.classEq (.cv x) A) (.imp ps ch)) x
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @g_nfv ch x
      (by
        first
        | (aesop))
  have p0003 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0004 := @g_spcimgft ps ch x A B p0002 p0003
  have p0005 :=
    @g_sylc ph (.all x (.imp (.classEq (.cv x) A) (.imp ps ch))) (.classMem A B)
      (.imp (.all x ps) ch) p0001 hyp_spcimdv_1 p0004
  exact p0005

@[expose]
noncomputable def g_spcimedv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_spcimdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_spcimedv_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (.imp ch ps))) :
    Nominal.NPrf (.imp ph (.imp ch (syn_wex x ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_con3d (syn_wa ph (.classEq (.cv x) A)) ch ps hyp_spcimedv_2
  have p0001 :=
    @g_spcimdv ph (.neg ps) (.neg ch) x A B
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      hyp_spcimdv_1 p0000
  have p0002 := @g_con2d ph (.all x (.neg ps)) ch p0001
  have p0003 := (Nominal.biimpRefl (syn_wex x ps))
  have p0004 := @g_syl6ibr ph ch (.neg (.all x (.neg ps))) (syn_wex x ps) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_spcgv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_spcgv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (.imp (.all x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 := @g_spcgf ph ps x A V p0000 p0001 hyp_spcgv_1
  exact p0002

@[expose]
noncomputable def g_spcegv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_spcgv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (.imp ps (syn_wex x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 := @g_spcegf ph ps x A V p0000 p0001 hyp_spcgv_1
  exact p0002

@[expose]
noncomputable def g_spc2egv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_spc2egv_1 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.imp ps (syn_wex x (syn_wex y ph)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪
      W.fv
  have p0000 :=
    @g_elisset x A V
      (by
        first
        | (aesop))
  have p0001 :=
    @g_elisset y B W
      (by
        first
        | (aesop))
  have p0002 :=
    @g_anim12i (.classMem A V) (syn_wex x (.classEq (.cv x) A)) (.classMem B W)
      (syn_wex y (.classEq (.cv y) B)) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq (.cv x) A) (.classEq (.cv y) B) x y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0004 :=
    @g_sylibr (syn_wa (.classMem A V) (.classMem B W))
      (syn_wa (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)))) p0002
      p0003
  have p0005 :=
    @g_biimprcd (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph ps hyp_spc2egv_1
  have p0006 :=
    @g_n_2eximdv ps (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0005
  have p0007 :=
    @g_syl5com (syn_wa (.classMem A V) (.classMem B W))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)))) ps
      (syn_wex x (syn_wex y ph)) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_spc2gv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_spc2egv_1 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.imp (.all x (.all y ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪
      W.fv
  have p0000 :=
    @g_notbid (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph ps hyp_spc2egv_1
  have p0001 :=
    @g_spc2egv (.neg ph) (.neg ps) x y A B V W
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_n_2nalexn ph x y
  have p0003 :=
    @g_syl6ibr (syn_wa (.classMem A V) (.classMem B W)) (.neg ps)
      (syn_wex x (syn_wex y (.neg ph))) (.neg (.all x (.all y ph))) p0001 p0002
  have p0004 :=
    @g_con4d (syn_wa (.classMem A V) (.classMem B W)) ps (.all x (.all y ph)) p0003
  exact p0004

@[expose]
noncomputable def g_spc3egv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (X : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_spc3egv_1 : Nominal.NPrf
        (.imp (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
        (.imp ps (syn_wex x (syn_wex y (syn_wex z ph))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
                A.fv ∪
              B.fv ∪
            C.fv ∪
          V.fv ∪
        W.fv ∪
      X.fv
  have p0000 :=
    @g_elisset x A V
      (by
        first
        | (aesop))
  have p0001 :=
    @g_elisset y B W
      (by
        first
        | (aesop))
  have p0002 :=
    @g_elisset z C X
      (by
        first
        | (aesop))
  have p0003 :=
    @g_n_3anim123i (.classMem A V) (syn_wex x (.classEq (.cv x) A)) (.classMem B W)
      (syn_wex y (.classEq (.cv y) B)) (.classMem C X) (syn_wex z (.classEq (.cv z) C))
      p0000 p0001 p0002
  have p0004 :=
    @g_eeeanv (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C) x y z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_sylibr (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
      (syn_w3a (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B))
        (syn_wex z (.classEq (.cv z) C)))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      p0003 p0004
  have p0006 :=
    @g_biimprcd (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      ph ps hyp_spc3egv_1
  have p0007 :=
    @g_eximdv ps (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      ph z
      (by
        first
        | (aesop))
      p0006
  have p0008 :=
    @g_n_2eximdv ps
      (syn_wex z (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))
      (syn_wex z ph) x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0007
  have p0009 :=
    @g_syl5com (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      ps (syn_wex x (syn_wex y (syn_wex z ph))) p0005 p0008
  exact p0009

@[expose]
noncomputable def g_spc3gv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (V : Class) (W : Class) (X : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_spc3egv_1 : Nominal.NPrf
        (.imp (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
        (.imp (.all x (.all y (.all z ph))) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
                A.fv ∪
              B.fv ∪
            C.fv ∪
          V.fv ∪
        W.fv ∪
      X.fv
  have p0000 :=
    @g_notbid (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph
      ps hyp_spc3egv_1
  have p0001 :=
    @g_spc3egv (.neg ph) (.neg ps) x y z A B C V W X
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_exnal ph z
  have p0003 := @g_exbii (syn_wex z (.neg ph)) (.neg (.all z ph)) y p0002
  have p0004 := @g_exnal (.all z ph) y
  have p0005 :=
    @g_bitri (syn_wex y (syn_wex z (.neg ph))) (syn_wex y (.neg (.all z ph)))
      (.neg (.all y (.all z ph))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wex y (syn_wex z (.neg ph))) (.neg (.all y (.all z ph))) x p0005
  have p0007 := @g_exnal (.all y (.all z ph)) x
  have p0008 :=
    @g_bitr2i (syn_wex x (syn_wex y (syn_wex z (.neg ph))))
      (syn_wex x (.neg (.all y (.all z ph)))) (.neg (.all x (.all y (.all z ph)))) p0006
      p0007
  have p0009 :=
    @g_syl6ibr (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) (.neg ps)
      (syn_wex x (syn_wex y (syn_wex z (.neg ph)))) (.neg (.all x (.all y (.all z ph))))
      p0001 p0008
  have p0010 :=
    @g_con4d (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) ps
      (.all x (.all y (.all z ph))) p0009
  exact p0010

@[expose]
noncomputable def g_spcv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_spcv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_spcv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_spcgv ph ps x A (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_spcv_2
  have p0001 := Nominal.mp hyp_spcv_1 p0000
  exact p0001

@[expose]
noncomputable def g_spcev (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_spcv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_spcv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp ps (syn_wex x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_spcegv ph ps x A (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_spcv_2
  have p0001 := Nominal.mp hyp_spcv_1 p0000
  exact p0001

@[expose]
noncomputable def g_spc2ev (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_spc2ev_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_spc2ev_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_spc2ev_3 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps))) :
    Nominal.NPrf (.imp ps (syn_wex x (syn_wex y ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_spc2egv ph ps x y A B (syn_cvv) (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_spc2ev_3
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.imp ps (syn_wex x (syn_wex y ph))) hyp_spc2ev_1 hyp_spc2ev_2 p0000
  exact p0001

@[expose]
noncomputable def g_rspc (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_rspc_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_rspc_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A B) (.imp (syn_wral x B ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := (Nominal.biimpRefl (syn_wral x B ph))
  have p0001 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfv (.classMem A B) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
  have p0003 := @g_nfim (.classMem A B) ps x p0002 hyp_rspc_1
  have p0004 := @g_eleq1 (.cv x) A B
  have p0005 :=
    @g_imbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0004
      hyp_rspc_2
  have p0006 :=
    @g_spcgf (.imp (.classMem (.cv x) B) ph) (.imp (.classMem A B) ps) x A B p0001 p0003
      p0005
  have p0007 :=
    @g_pm2_43a (.all x (.imp (.classMem (.cv x) B) ph)) (.classMem A B) ps p0006
  have p0008 :=
    @g_syl5bi (syn_wral x B ph) (.all x (.imp (.classMem (.cv x) B) ph)) (.classMem A B)
      ps p0000 p0007
  exact p0008

@[expose]
noncomputable def g_rspce (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_rspc_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_rspc_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A B) ps) (syn_wrex x B ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv (.classMem A B) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
  have p0002 := @g_nfan (.classMem A B) ps x p0001 hyp_rspc_1
  have p0003 := @g_eleq1 (.cv x) A B
  have p0004 :=
    @g_anbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0003
      hyp_rspc_2
  have p0005 :=
    @g_spcegf (syn_wa (.classMem (.cv x) B) ph) (syn_wa (.classMem A B) ps) x A B p0000
      p0002 p0004
  have p0006 :=
    @g_anabsi5 (.classMem A B) ps (syn_wex x (syn_wa (.classMem (.cv x) B) ph)) p0005
  have p0007 := (Nominal.biimpRefl (syn_wrex x B ph))
  have p0008 :=
    @g_sylibr (syn_wa (.classMem A B) ps) (syn_wex x (syn_wa (.classMem (.cv x) B) ph))
      (syn_wrex x B ph) p0006 p0007
  exact p0008

@[expose]
noncomputable def g_rspcv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A B) (.imp (syn_wral x B ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_rspc ph ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 hyp_rspcv_1
  exact p0001

@[expose]
noncomputable def g_rspccv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_wral x B ph) (.imp (.classMem A B) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rspcv ph ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_rspcv_1
  have p0001 := @g_com12 (.classMem A B) (syn_wral x B ph) ps p0000
  exact p0001

@[expose]
noncomputable def g_rspcva (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A B) (syn_wral x B ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rspcv ph ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_rspcv_1
  have p0001 := @g_imp (.classMem A B) (syn_wral x B ph) ps p0000
  exact p0001

@[expose]
noncomputable def g_rspccva (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_wa (syn_wral x B ph) (.classMem A B)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rspcv ph ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_rspcv_1
  have p0001 := @g_impcom (.classMem A B) (syn_wral x B ph) ps p0000
  exact p0001

@[expose]
noncomputable def g_rspcev (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A B) ps) (syn_wrex x B ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_rspce ph ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 hyp_rspcv_1
  exact p0001

@[expose]
noncomputable def g_rspcimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_x : x ∉ ph.fv) (hyp_rspcimdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_rspcimdv_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wral x B ps) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := (Nominal.biimpRefl (syn_wral x B ps))
  have p0001 := @g_simpr ph (.classEq (.cv x) A)
  have p0002 := @g_eleq1d (syn_wa ph (.classEq (.cv x) A)) (.cv x) A B p0001
  have p0003 :=
    @g_biimprd (syn_wa ph (.classEq (.cv x) A)) (.classMem (.cv x) B) (.classMem A B)
      p0002
  have p0004 :=
    @g_imim12d (syn_wa ph (.classEq (.cv x) A)) (.classMem A B) (.classMem (.cv x) B) ps
      ch p0003 hyp_rspcimdv_2
  have p0005 :=
    @g_spcimdv ph (.imp (.classMem (.cv x) B) ps) (.imp (.classMem A B) ch) x A B
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      hyp_rspcimdv_1 p0004
  have p0006 :=
    @g_mpid ph (.all x (.imp (.classMem (.cv x) B) ps)) (.classMem A B) ch hyp_rspcimdv_1
      p0005
  have p0007 :=
    @g_syl5bi (syn_wral x B ps) (.all x (.imp (.classMem (.cv x) B) ps)) ph ch p0000 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay
