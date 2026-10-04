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

/-- Checked nominal proof certificate identified upstream as `g_nfcrd`. -/
@[expose]
noncomputable def gNfcrd (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) (hyp_nfeqd_1 : Nominal.NPrf (.imp ph (synWnfc x A))) :
    Nominal.NPrf (.imp ph (synWnf x (.classMem (.cv y) A))) :=
  by
  have p0000 :=
    @gNfcr x y A
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gSyl ph (synWnfc x A) (synWnf x (.classMem (.cv y) A)) hyp_nfeqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfeqd`. -/
@[expose]
noncomputable def gNfeqd (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfeqd_1 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_nfeqd_2 : Nominal.NPrf (.imp ph (synWnfc x B))) :
    Nominal.NPrf (.imp ph (synWnf x (.classEq A B))) :=
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
    @gDfcleq y A B
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gNfv ph y
      (by
        aesop)
  have p0002 :=
    @gNfcrd ph x y A
      (by
        aesop)
      (by
        aesop)
      hyp_nfeqd_1
  have p0003 :=
    @gNfcrd ph x y B
      (by
        aesop)
      (by
        aesop)
      hyp_nfeqd_2
  have p0004 := @gNfbid ph (.classMem (.cv y) A) (.classMem (.cv y) B) x p0002 p0003
  have p0005 :=
    @gNfald ph (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)) x y p0001 p0004
  have p0006 :=
    @gNfxfrd (.classEq A B) (.all y (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)))
      ph x p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_nfeld`. -/
@[expose]
noncomputable def gNfeld (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfeqd_1 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_nfeqd_2 : Nominal.NPrf (.imp ph (synWnfc x B))) :
    Nominal.NPrf (.imp ph (synWnf x (.classMem A B))) :=
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
        aesop) (by
        aesop))
  have p0001 :=
    @gNfv ph y
      (by
        aesop)
  have p0002 :=
    @gNfcvd ph x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 := @gNfeqd ph x (.cv y) A p0002 hyp_nfeqd_1
  have p0004 :=
    @gNfcrd ph x y B
      (by
        aesop)
      (by
        aesop)
      hyp_nfeqd_2
  have p0005 := @gNfand ph (.classEq (.cv y) A) (.classMem (.cv y) B) x p0003 p0004
  have p0006 :=
    @gNfexd ph (synWa (.classEq (.cv y) A) (.classMem (.cv y) B)) x y p0001 p0005
  have p0007 :=
    @gNfxfrd (.classMem A B)
      (synWex y (synWa (.classEq (.cv y) A) (.classMem (.cv y) B))) ph x p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_drnfc1`. -/
@[expose]
noncomputable def gDrnfc1 (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_drnfc1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (.classEq A B))) :
    Nominal.NPrf
      (.imp (.all x (.classEq (.cv x) (.cv y))) (synWb (synWnfc x A) (synWnfc y B))) :=
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
    @gEleq2d (.all x (.classEq (.cv x) (.cv y))) A B (.cv w) p0000_e00_recanon
  have p0001_e00_recanon :
    Nominal.NPrf
      (.imp (.all x (.objEq x y)) (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0001 := @gDrnf1 (.classMem (.cv w) A) (.classMem (.cv w) B) x y p0001_e00_recanon
  have p0002 :=
    @gDral2 (synWnf x (.classMem (.cv w) A)) (synWnf y (.classMem (.cv w) B)) x y w
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x w A
      (by
        aesop)
      (by
        aesop)
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc y w B
      (by
        aesop)
      (by
        aesop)
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.all x (.classEq (.cv x) (.cv y)))
        (synWb (.all w (synWnf x (.classMem (.cv w) A)))
          (.all w (synWnf y (.classMem (.cv w) B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0005 :=
    @gN3bitr4g (.all x (.classEq (.cv x) (.cv y)))
      (.all w (synWnf x (.classMem (.cv w) A)))
      (.all w (synWnf y (.classMem (.cv w) B))) (synWnfc x A) (synWnfc y B)
      p0005_e00_recanon p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfabd2`. -/
@[expose]
noncomputable def gNfabd2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfabd2_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfabd2_2 :
      Nominal.NPrf (.imp (synWa ph (.neg (.all x (.objEq x y)))) (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnfc x (.cab y ps))) :=
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
    @gNfv (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) z
      (by
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
  have p0002 := @gNfnae x y y
  have p0003_e01_recanon :
    Nominal.NPrf (synWnf y (.neg (.all x (.classEq (.cv x) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWnf
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
    @gNfan ph (.neg (.all x (.classEq (.cv x) (.cv y)))) y hyp_nfabd2_1 p0003_e01_recanon
  have p0004_e01_recanon :
    Nominal.NPrf
      (.imp (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) (synWnf x ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWnf
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
    @gNfsbd (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) ps y z x
      (by
        aesop)
      p0003 p0004_e01_recanon
  have p0005 :=
    @gNfxfrd (.classMem (.cv z) (.cab y ps)) (synWsb z y ps)
      (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) x p0001 p0004
  have p0006 :=
    @gNfcd (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) x z (.cab y ps)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        aesop)
      p0000 p0005
  have p0007 :=
    @gEx ph (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnfc x (.cab y ps)) p0006
  have p0008 := @gNfab1 ps y
  have p0009 := @gEqidd (.all x (.classEq (.cv x) (.cv y))) (.cab y ps)
  have p0010_e00_recanon :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.classEq (.cab y ps) (.cab y ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 := @gDrnfc1 x y (.cab y ps) (.cab y ps) p0010_e00_recanon
  have p0011 :=
    @gMpbiri (.all x (.classEq (.cv x) (.cv y))) (synWnfc x (.cab y ps))
      (synWnfc y (.cab y ps)) p0008 p0010
  have p0012 :=
    @gPm261d2 ph (.all x (.classEq (.cv x) (.cv y))) (synWnfc x (.cab y ps)) p0007
      p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_nfabd`. -/
@[expose]
noncomputable def gNfabd (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfabd_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfabd_2 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnfc x (.cab y ps))) :=
  by
  have p0000 :=
    @gAdantr ph (synWnf x ps) (.neg (.all x (.classEq (.cv x) (.cv y)))) hyp_nfabd_2
  have p0001_e01_recanon :
    Nominal.NPrf (.imp (synWa ph (.neg (.all x (.objEq x y)))) (synWnf x ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWnf
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
  have p0001 := @gNfabd2 ph ps x y hyp_nfabd_1 p0001_e01_recanon
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dvelimdc`. -/
@[expose]
noncomputable def gDvelimdc (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (hyp_dvelimdc_1 : Nominal.NPrf (synWnf x ph))
    (hyp_dvelimdc_2 : Nominal.NPrf (synWnf z ph))
    (hyp_dvelimdc_3 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_dvelimdc_4 : Nominal.NPrf (.imp ph (synWnfc z B)))
    (hyp_dvelimdc_5 : Nominal.NPrf (.imp ph (.imp (.objEq z y) (.classEq A B)))) :
    Nominal.NPrf
      (.imp ph (.imp (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnfc x B))) :=
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
    @gNfv (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) w
      (by
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
    @gNfcrd ph x w A
      (by
        aesop)
      (by
        aesop)
      hyp_dvelimdc_3
  have p0002 :=
    @gNfcrd ph z w B
      (by
        aesop)
      (by
        aesop)
      hyp_dvelimdc_4
  have p0003 := @gEleq2 A B (.cv w)
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
    @gSyl6 ph (.classEq (.cv z) (.cv y)) (.classEq A B)
      (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)) p0004_e00_recanon p0003
  have p0005_e04_recanon :
    Nominal.NPrf
      (.imp ph (.imp (.objEq z y) (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gDvelimdf ph (.classMem (.cv w) A) (.classMem (.cv w) B) x y z hyp_dvelimdc_1
      hyp_dvelimdc_2 p0001 p0002 p0005_e04_recanon
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp ph (.imp (.neg (.all x (.classEq (.cv x) (.cv y))))
          (synWnf x (.classMem (.cv w) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gImp ph (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnf x (.classMem (.cv w) B))
      p0006_e00_recanon
  have p0007 :=
    @gNfcd (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) x w B
      (by
        aesop)
      (by
        aesop)
      p0000 p0006
  have p0008 := @gEx ph (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnfc x B) p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_dvelimc`. -/
@[expose]
noncomputable def gDvelimc (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (hyp_dvelimc_1 : Nominal.NPrf (synWnfc x A))
    (hyp_dvelimc_2 : Nominal.NPrf (synWnfc z B))
    (hyp_dvelimc_3 : Nominal.NPrf (.imp (.objEq z y) (.classEq A B))) :
    Nominal.NPrf (.imp (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnfc x B)) :=
  by
  have p0000 := @gNftru x
  have p0001 := @gNftru z
  have p0002 := @gA1i (synWnfc x A) synWtru hyp_dvelimc_1
  have p0003 := @gA1i (synWnfc z B) synWtru hyp_dvelimc_2
  have p0004_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv z) (.cv y)) (.classEq A B)) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_dvelimc_3
  have p0004 :=
    @gA1i (.imp (.classEq (.cv z) (.cv y)) (.classEq A B)) synWtru p0004_e00_recanon
  have p0005_e04_recanon :
    Nominal.NPrf (.imp synWtru (.imp (.objEq z y) (.classEq A B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWtru
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 := @gDvelimdc synWtru x y z A B p0000 p0001 p0002 p0003 p0005_e04_recanon
  have p0006 :=
    @gTrud (.imp (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnfc x B)) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_nfcvf`. -/
@[expose]
noncomputable def gNfcvf (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnfc x (.cv y))) :=
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
    @gNfcv x (.cv z)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 :=
    @gNfcv z (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @gId (.classEq (.cv z) (.cv y))
  have p0003_e02_recanon : Nominal.NPrf (.imp (.objEq z y) (.classEq (.cv z) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 := @gDvelimc x y z (.cv z) (.cv y) p0000 p0001 p0003_e02_recanon
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cleqf`. -/
@[expose]
noncomputable def gCleqf (x : Var) (A : Class) (B : Class)
    (hyp_cleqf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_cleqf_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf
      (synWb (.classEq A B) (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
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
    @gDfcleq y A B
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gNfv (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 :=
    @gNfcri x y A
      (by
        aesop)
      hyp_cleqf_1
  have p0003 :=
    @gNfcri x y B
      (by
        aesop)
      hyp_cleqf_2
  have p0004 := @gNfbi (.classMem (.cv y) A) (.classMem (.cv y) B) x p0002 p0003
  have p0005 := @gEleq1 (.cv x) (.cv y) A
  have p0006 := @gEleq1 (.cv x) (.cv y) B
  have p0007 :=
    @gBibi12d (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0005 p0006
  have p0008_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
          (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gCbval (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)) x y p0001 p0004
      p0008_e02_recanon
  have p0009 :=
    @gBitr4i (.classEq A B) (.all y (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)))
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_nne`. -/
@[expose]
noncomputable def gNne (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.neg (synWne A B)) (.classEq A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWne A B))
  have p0001 := @gCon2bii (synWne A B) (.classEq A B) p0000
  have p0002 := @gBicomi (.classEq A B) (.neg (synWne A B)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_neirr`. -/
@[expose]
noncomputable def gNeirr (A : Class) : Nominal.NPrf (.neg (synWne A A)) :=
  by
  have p0000 := @gEqid A
  have p0001 := @gNne A A
  have p0002 := @gMpbir (.neg (synWne A A)) (.classEq A A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_neeq1`. -/
@[expose]
noncomputable def gNeeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWne A C) (synWne B C))) :=
  by
  have p0000 := @gEqeq1 A B C
  have p0001 := @gNotbid (.classEq A B) (.classEq A C) (.classEq B C) p0000
  have p0002 := (Nominal.biimpRefl (synWne A C))
  have p0003 := (Nominal.biimpRefl (synWne B C))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (.neg (.classEq A C)) (.neg (.classEq B C)) (synWne A C)
      (synWne B C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_neeq2`. -/
@[expose]
noncomputable def gNeeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWne C A) (synWne C B))) :=
  by
  have p0000 := @gEqeq2 A B C
  have p0001 := @gNotbid (.classEq A B) (.classEq C A) (.classEq C B) p0000
  have p0002 := (Nominal.biimpRefl (synWne C A))
  have p0003 := (Nominal.biimpRefl (synWne C B))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (.neg (.classEq C A)) (.neg (.classEq C B)) (synWne C A)
      (synWne C B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_neeq1i`. -/
@[expose]
noncomputable def gNeeq1i (A : Class) (B : Class) (C : Class)
    (hyp_neeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWne A C) (synWne B C)) :=
  by
  have p0000 := @gNeeq1 A B C
  have p0001 := Nominal.mp hyp_neeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_neeq2i`. -/
@[expose]
noncomputable def gNeeq2i (A : Class) (B : Class) (C : Class)
    (hyp_neeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWne C A) (synWne C B)) :=
  by
  have p0000 := @gNeeq2 A B C
  have p0001 := Nominal.mp hyp_neeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_neeq1d`. -/
@[expose]
noncomputable def gNeeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_neeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWne A C) (synWne B C))) :=
  by
  have p0000 := @gNeeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWne A C) (synWne B C)) hyp_neeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_neeq2d`. -/
@[expose]
noncomputable def gNeeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_neeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWne C A) (synWne C B))) :=
  by
  have p0000 := @gNeeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWne C A) (synWne C B)) hyp_neeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_neeq12d`. -/
@[expose]
noncomputable def gNeeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_neeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_neeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (synWb (synWne A C) (synWne B D))) :=
  by
  have p0000 := @gNeeq1d ph A B C hyp_neeq1d_1
  have p0001 := @gNeeq2d ph C D B hyp_neeq12d_2
  have p0002 := @gBitrd ph (synWne A C) (synWne B C) (synWne B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_neneqd`. -/
@[expose]
noncomputable def gNeneqd (ph : Wff) (A : Class) (B : Class)
    (hyp_neneqd_1 : Nominal.NPrf (.imp ph (synWne A B))) :
    Nominal.NPrf (.imp ph (.neg (.classEq A B))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWne A B))
  have p0001 := @gSylib ph (synWne A B) (.neg (.classEq A B)) hyp_neneqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqnetri`. -/
@[expose]
noncomputable def gEqnetri (A : Class) (B : Class) (C : Class)
    (hyp_eqnetr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqnetr_2 : Nominal.NPrf (synWne B C)) : Nominal.NPrf (synWne A C) :=
  by
  have p0000 := @gNeeq1i A B C hyp_eqnetr_1
  have p0001 := @gMpbir (synWne A C) (synWne B C) hyp_eqnetr_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqnetrd`. -/
@[expose]
noncomputable def gEqnetrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqnetrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqnetrd_2 : Nominal.NPrf (.imp ph (synWne B C))) :
    Nominal.NPrf (.imp ph (synWne A C)) :=
  by
  have p0000 := @gNeeq1d ph A B C hyp_eqnetrd_1
  have p0001 := @gMpbird ph (synWne A C) (synWne B C) hyp_eqnetrd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqnetrri`. -/
@[expose]
noncomputable def gEqnetrri (A : Class) (B : Class) (C : Class)
    (hyp_eqnetrr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqnetrr_2 : Nominal.NPrf (synWne A C)) : Nominal.NPrf (synWne B C) :=
  by
  have p0000 := @gEqcomi A B hyp_eqnetrr_1
  have p0001 := @gEqnetri B A C p0000 hyp_eqnetrr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqnetrrd`. -/
@[expose]
noncomputable def gEqnetrrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqnetrrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqnetrrd_2 : Nominal.NPrf (.imp ph (synWne A C))) :
    Nominal.NPrf (.imp ph (synWne B C)) :=
  by
  have p0000 := @gEqcomd ph A B hyp_eqnetrrd_1
  have p0001 := @gEqnetrd ph B A C p0000 hyp_eqnetrrd_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_necon3abii`. -/
@[expose]
noncomputable def gNecon3abii (ph : Wff) (A : Class) (B : Class)
    (hyp_necon3abii_1 : Nominal.NPrf (synWb (.classEq A B) ph)) :
    Nominal.NPrf (synWb (synWne A B) (.neg ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWne A B))
  have p0001 := @gXchbinx (synWne A B) (.classEq A B) ph p0000 hyp_necon3abii_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_necon3bbii`. -/
@[expose]
noncomputable def gNecon3bbii (ph : Wff) (A : Class) (B : Class)
    (hyp_necon3bbii_1 : Nominal.NPrf (synWb ph (.classEq A B))) :
    Nominal.NPrf (synWb (.neg ph) (synWne A B)) :=
  by
  have p0000 := @gBicomi ph (.classEq A B) hyp_necon3bbii_1
  have p0001 := @gNecon3abii ph A B p0000
  have p0002 := @gBicomi (synWne A B) (.neg ph) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3bii`. -/
@[expose]
noncomputable def gNecon3bii (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon3bii_1 : Nominal.NPrf (synWb (.classEq A B) (.classEq C D))) :
    Nominal.NPrf (synWb (synWne A B) (synWne C D)) :=
  by
  have p0000 := @gNecon3abii (.classEq C D) A B hyp_necon3bii_1
  have p0001 := (Nominal.biimpRefl (synWne C D))
  have p0002 := @gBitr4i (synWne A B) (.neg (.classEq C D)) (synWne C D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3abid`. -/
@[expose]
noncomputable def gNecon3abid (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon3abid_1 : Nominal.NPrf (.imp ph (synWb (.classEq A B) ps))) :
    Nominal.NPrf (.imp ph (synWb (synWne A B) (.neg ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWne A B))
  have p0001 := @gNotbid ph (.classEq A B) ps hyp_necon3abid_1
  have p0002 := @gSyl5bb (synWne A B) (.neg (.classEq A B)) ph (.neg ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3bbid`. -/
@[expose]
noncomputable def gNecon3bbid (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon3bbid_1 : Nominal.NPrf (.imp ph (synWb ps (.classEq A B)))) :
    Nominal.NPrf (.imp ph (synWb (.neg ps) (synWne A B))) :=
  by
  have p0000 := @gBicomd ph ps (.classEq A B) hyp_necon3bbid_1
  have p0001 := @gNecon3abid ph ps A B p0000
  have p0002 := @gBicomd ph (synWne A B) (.neg ps) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3ad`. -/
@[expose]
noncomputable def gNecon3ad (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon3ad_1 : Nominal.NPrf (.imp ph (.imp ps (.classEq A B)))) :
    Nominal.NPrf (.imp ph (.imp (synWne A B) (.neg ps))) :=
  by
  have p0000 := @gNne A B
  have p0001 := @gSyl6ibr ph ps (.classEq A B) (.neg (synWne A B)) hyp_necon3ad_1 p0000
  have p0002 := @gCon2d ph ps (synWne A B) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3bd`. -/
@[expose]
noncomputable def gNecon3bd (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon3bd_1 : Nominal.NPrf (.imp ph (.imp (.classEq A B) ps))) :
    Nominal.NPrf (.imp ph (.imp (.neg ps) (synWne A B))) :=
  by
  have p0000 := @gNne A B
  have p0001 := @gSyl5bi (.neg (synWne A B)) (.classEq A B) ph ps p0000 hyp_necon3bd_1
  have p0002 := @gCon1d ph (synWne A B) ps p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3d`. -/
@[expose]
noncomputable def gNecon3d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon3d_1 : Nominal.NPrf (.imp ph (.imp (.classEq A B) (.classEq C D)))) :
    Nominal.NPrf (.imp ph (.imp (synWne C D) (synWne A B))) :=
  by
  have p0000 := @gNecon3ad ph (.classEq A B) C D hyp_necon3d_1
  have p0001 := (Nominal.biimpRefl (synWne A B))
  have p0002 :=
    @gSyl6ibr ph (synWne C D) (.neg (.classEq A B)) (synWne A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3i`. -/
@[expose]
noncomputable def gNecon3i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon3i_1 : Nominal.NPrf (.imp (.classEq A B) (.classEq C D))) :
    Nominal.NPrf (.imp (synWne C D) (synWne A B)) :=
  by
  have p0000 := @gId (.imp (.classEq A B) (.classEq C D))
  have p0001 := @gNecon3d (.imp (.classEq A B) (.classEq C D)) A B C D p0000
  have p0002 := Nominal.mp hyp_necon3i_1 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3ai`. -/
@[expose]
noncomputable def gNecon3ai (ph : Wff) (A : Class) (B : Class)
    (hyp_necon3ai_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp (synWne A B) (.neg ph)) :=
  by
  have p0000 := @gNne A B
  have p0001 := @gSylibr ph (.classEq A B) (.neg (synWne A B)) hyp_necon3ai_1 p0000
  have p0002 := @gCon2i ph (synWne A B) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon3bi`. -/
@[expose]
noncomputable def gNecon3bi (ph : Wff) (A : Class) (B : Class)
    (hyp_necon3bi_1 : Nominal.NPrf (.imp (.classEq A B) ph)) :
    Nominal.NPrf (.imp (.neg ph) (synWne A B)) :=
  by
  have p0000 := @gNne A B
  have p0001 := @gSylbi (.neg (synWne A B)) (.classEq A B) ph p0000 hyp_necon3bi_1
  have p0002 := @gCon1i (synWne A B) ph p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon1ai`. -/
@[expose]
noncomputable def gNecon1ai (ph : Wff) (A : Class) (B : Class)
    (hyp_necon1ai_1 : Nominal.NPrf (.imp (.neg ph) (.classEq A B))) :
    Nominal.NPrf (.imp (synWne A B) ph) :=
  by
  have p0000 := (Nominal.biimpRefl (synWne A B))
  have p0001 := @gCon1i ph (.classEq A B) hyp_necon1ai_1
  have p0002 := @gSylbi (synWne A B) (.neg (.classEq A B)) ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon1bi`. -/
@[expose]
noncomputable def gNecon1bi (ph : Wff) (A : Class) (B : Class)
    (hyp_necon1bi_1 : Nominal.NPrf (.imp (synWne A B) ph)) :
    Nominal.NPrf (.imp (.neg ph) (.classEq A B)) :=
  by
  have p0000 := @gCon3i (synWne A B) ph hyp_necon1bi_1
  have p0001 := @gNne A B
  have p0002 := @gSylib (.neg ph) (.neg (synWne A B)) (.classEq A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon2ai`. -/
@[expose]
noncomputable def gNecon2ai (ph : Wff) (A : Class) (B : Class)
    (hyp_necon2ai_1 : Nominal.NPrf (.imp (.classEq A B) (.neg ph))) :
    Nominal.NPrf (.imp ph (synWne A B)) :=
  by
  have p0000 := @gNne A B
  have p0001 :=
    @gSylbi (.neg (synWne A B)) (.classEq A B) (.neg ph) p0000 hyp_necon2ai_1
  have p0002 := @gCon4i (synWne A B) ph p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon2bi`. -/
@[expose]
noncomputable def gNecon2bi (ph : Wff) (A : Class) (B : Class)
    (hyp_necon2bi_1 : Nominal.NPrf (.imp ph (synWne A B))) :
    Nominal.NPrf (.imp (.classEq A B) (.neg ph)) :=
  by
  have p0000 := @gNeneqd ph A B hyp_necon2bi_1
  have p0001 := @gCon2i ph (.classEq A B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_necon2ad`. -/
@[expose]
noncomputable def gNecon2ad (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon2ad_1 : Nominal.NPrf (.imp ph (.imp (.classEq A B) (.neg ps)))) :
    Nominal.NPrf (.imp ph (.imp ps (synWne A B))) :=
  by
  have p0000 := @gNne A B
  have p0001 :=
    @gSyl5bi (.neg (synWne A B)) (.classEq A B) ph (.neg ps) p0000 hyp_necon2ad_1
  have p0002 := @gCon4d ph (synWne A B) ps p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon2bd`. -/
@[expose]
noncomputable def gNecon2bd (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_necon2bd_1 : Nominal.NPrf (.imp ph (.imp ps (synWne A B)))) :
    Nominal.NPrf (.imp ph (.imp (.classEq A B) (.neg ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWne A B))
  have p0001 := @gSyl6ib ph ps (synWne A B) (.neg (.classEq A B)) hyp_necon2bd_1 p0000
  have p0002 := @gCon2d ph ps (.classEq A B) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon1bbii`. -/
@[expose]
noncomputable def gNecon1bbii (ph : Wff) (A : Class) (B : Class)
    (hyp_necon1bbii_1 : Nominal.NPrf (synWb (synWne A B) ph)) :
    Nominal.NPrf (synWb (.neg ph) (.classEq A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWne A B))
  have p0001 := @gBitr3i (.neg (.classEq A B)) (synWne A B) ph p0000 hyp_necon1bbii_1
  have p0002 := @gCon1bii (.classEq A B) ph p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon2bbii`. -/
@[expose]
noncomputable def gNecon2bbii (ph : Wff) (A : Class) (B : Class)
    (hyp_necon2bbii_1 : Nominal.NPrf (synWb ph (synWne A B))) :
    Nominal.NPrf (synWb (.classEq A B) (.neg ph)) :=
  by
  have p0000 := @gBicomi ph (synWne A B) hyp_necon2bbii_1
  have p0001 := @gNecon1bbii ph A B p0000
  have p0002 := @gBicomi (.neg ph) (.classEq A B) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon4i`. -/
@[expose]
noncomputable def gNecon4i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon4i_1 : Nominal.NPrf (.imp (synWne A B) (synWne C D))) :
    Nominal.NPrf (.imp (.classEq C D) (.classEq A B)) :=
  by
  have p0000 := @gNecon2bi (synWne A B) C D hyp_necon4i_1
  have p0001 := @gNne A B
  have p0002 := @gSylib (.classEq C D) (.neg (synWne A B)) (.classEq A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necon4d`. -/
@[expose]
noncomputable def gNecon4d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_necon4d_1 : Nominal.NPrf (.imp ph (.imp (synWne A B) (synWne C D)))) :
    Nominal.NPrf (.imp ph (.imp (.classEq C D) (.classEq A B))) :=
  by
  have p0000 := @gNecon2bd ph (synWne A B) C D hyp_necon4d_1
  have p0001 := @gNne A B
  have p0002 :=
    @gSyl6ib ph (.classEq C D) (.neg (synWne A B)) (.classEq A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm2_21ddne`. -/
@[expose]
noncomputable def gPm221ddne (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_pm2_21ddne_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_pm2_21ddne_2 : Nominal.NPrf (.imp ph (synWne A B))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gNeneqd ph A B hyp_pm2_21ddne_2
  have p0001 := @gPm221dd ph (.classEq A B) ps hyp_pm2_21ddne_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_61ine`. -/
@[expose]
noncomputable def gPm261ine (ph : Wff) (A : Class) (B : Class)
    (hyp_pm2_61ine_1 : Nominal.NPrf (.imp (.classEq A B) ph))
    (hyp_pm2_61ine_2 : Nominal.NPrf (.imp (synWne A B) ph)) : Nominal.NPrf ph :=
  by
  have p0000 := @gNne A B
  have p0001 := @gSylbi (.neg (synWne A B)) (.classEq A B) ph p0000 hyp_pm2_61ine_1
  have p0002 := @gPm261i (synWne A B) ph hyp_pm2_61ine_2 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm2_61dne`. -/
@[expose]
noncomputable def gPm261dne (ph : Wff) (ps : Wff) (A : Class) (B : Class)
    (hyp_pm2_61dne_1 : Nominal.NPrf (.imp ph (.imp (.classEq A B) ps)))
    (hyp_pm2_61dne_2 : Nominal.NPrf (.imp ph (.imp (synWne A B) ps))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gNne A B
  have p0001 := @gSyl5bi (.neg (synWne A B)) (.classEq A B) ph ps p0000 hyp_pm2_61dne_1
  have p0002 := @gPm261d ph (synWne A B) ps hyp_pm2_61dne_2 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_necom`. -/
@[expose]
noncomputable def gNecom (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWne A B) (synWne B A)) :=
  by
  have p0000 := @gEqcom A B
  have p0001 := @gNecon3bii A B B A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_necomi`. -/
@[expose]
noncomputable def gNecomi (A : Class) (B : Class)
    (hyp_necomi_1 : Nominal.NPrf (synWne A B)) : Nominal.NPrf (synWne B A) :=
  by
  have p0000 := @gNecom A B
  have p0001 := @gMpbi (synWne A B) (synWne B A) hyp_necomi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_necomd`. -/
@[expose]
noncomputable def gNecomd (ph : Wff) (A : Class) (B : Class)
    (hyp_necomd_1 : Nominal.NPrf (.imp ph (synWne A B))) :
    Nominal.NPrf (.imp ph (synWne B A)) :=
  by
  have p0000 := @gNecom A B
  have p0001 := @gSylib ph (synWne A B) (synWne B A) hyp_necomd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nelne2`. -/
@[expose]
noncomputable def gNelne2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWa (.classMem A C) (.neg (.classMem B C))) (synWne A B)) :=
  by
  have p0000 := @gEleq1 A B C
  have p0001 := @gBiimpcd (.classEq A B) (.classMem A C) (.classMem B C) p0000
  have p0002 := @gNecon3bd (.classMem A C) (.classMem B C) A B p0001
  have p0003 := @gImp (.classMem A C) (.neg (.classMem B C)) (synWne A B) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ralnex`. -/
@[expose]
noncomputable def gRalnex (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (synWb (synWral x A (.neg ph)) (.neg (synWrex x A ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x A (.neg ph)))
  have p0001 := @gAlinexa (.classMem (.cv x) A) ph x
  have p0002 := (Nominal.biimpRefl (synWrex x A ph))
  have p0003 :=
    @gXchbinxr (.all x (.imp (.classMem (.cv x) A) (.neg ph)))
      (synWex x (synWa (.classMem (.cv x) A) ph)) (synWrex x A ph) p0001 p0002
  have p0004 :=
    @gBitri (synWral x A (.neg ph)) (.all x (.imp (.classMem (.cv x) A) (.neg ph)))
      (.neg (synWrex x A ph)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_rexnal`. -/
@[expose]
noncomputable def gRexnal (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (synWb (synWrex x A (.neg ph)) (.neg (synWral x A ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWrex x A (.neg ph)))
  have p0001 := @gExanali (.classMem (.cv x) A) ph x
  have p0002 := (Nominal.biimpRefl (synWral x A ph))
  have p0003 :=
    @gXchbinxr (synWex x (synWa (.classMem (.cv x) A) (.neg ph)))
      (.all x (.imp (.classMem (.cv x) A) ph)) (synWral x A ph) p0001 p0002
  have p0004 :=
    @gBitri (synWrex x A (.neg ph)) (synWex x (synWa (.classMem (.cv x) A) (.neg ph)))
      (.neg (synWral x A ph)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dfral2`. -/
@[expose]
noncomputable def gDfral2 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (synWb (synWral x A ph) (.neg (synWrex x A (.neg ph)))) :=
  by
  have p0000 := @gRexnal ph x A
  have p0001 := @gCon2bii (synWrex x A (.neg ph)) (synWral x A ph) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfrex2`. -/
@[expose]
noncomputable def gDfrex2 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (synWb (synWrex x A ph) (.neg (synWral x A (.neg ph)))) :=
  by
  have p0000 := @gRalnex ph x A
  have p0001 := @gCon2bii (synWral x A (.neg ph)) (synWrex x A ph) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralbida`. -/
@[expose]
noncomputable def gRalbida (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralbida_1 : Nominal.NPrf (synWnf x ph))
    (hyp_ralbida_2 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 := @gPm574da ph (.classMem (.cv x) A) ps ch hyp_ralbida_2
  have p0001 :=
    @gAlbid ph (.imp (.classMem (.cv x) A) ps) (.imp (.classMem (.cv x) A) ch) x
      hyp_ralbida_1 p0000
  have p0002 := (Nominal.biimpRefl (synWral x A ps))
  have p0003 := (Nominal.biimpRefl (synWral x A ch))
  have p0004 :=
    @gN3bitr4g ph (.all x (.imp (.classMem (.cv x) A) ps))
      (.all x (.imp (.classMem (.cv x) A) ch)) (synWral x A ps) (synWral x A ch) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_rexbida`. -/
@[expose]
noncomputable def gRexbida (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralbida_1 : Nominal.NPrf (synWnf x ph))
    (hyp_ralbida_2 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 := @gPm532da ph (.classMem (.cv x) A) ps ch hyp_ralbida_2
  have p0001 :=
    @gExbid ph (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv x) A) ch) x
      hyp_ralbida_1 p0000
  have p0002 := (Nominal.biimpRefl (synWrex x A ps))
  have p0003 := (Nominal.biimpRefl (synWrex x A ch))
  have p0004 :=
    @gN3bitr4g ph (synWex x (synWa (.classMem (.cv x) A) ps))
      (synWex x (synWa (.classMem (.cv x) A) ch)) (synWrex x A ps) (synWrex x A ch)
      p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ralbidva`. -/
@[expose]
noncomputable def gRalbidva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralbidva_1 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gRalbida ph ps ch x A p0000 hyp_ralbidva_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexbidva`. -/
@[expose]
noncomputable def gRexbidva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralbidva_1 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gRexbida ph ps ch x A p0000 hyp_ralbidva_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralbid`. -/
@[expose]
noncomputable def gRalbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralbid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_ralbid_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 := @gAdantr ph (synWb ps ch) (.classMem (.cv x) A) hyp_ralbid_2
  have p0001 := @gRalbida ph ps ch x A hyp_ralbid_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexbid`. -/
@[expose]
noncomputable def gRexbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralbid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_ralbid_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 := @gAdantr ph (synWb ps ch) (.classMem (.cv x) A) hyp_ralbid_2
  have p0001 := @gRexbida ph ps ch x A hyp_ralbid_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralbidv`. -/
@[expose]
noncomputable def gRalbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gRalbid ph ps ch x A p0000 hyp_ralbidv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexbidv`. -/
@[expose]
noncomputable def gRexbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gRexbid ph ps ch x A p0000 hyp_ralbidv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexbidv2`. -/
@[expose]
noncomputable def gRexbidv2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexbidv2_1 : Nominal.NPrf (.imp ph
          (synWb (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv x) B) ch)))) :
    Nominal.NPrf (.imp ph (synWb (synWrex x A ps) (synWrex x B ch))) :=
  by
  have p0000 :=
    @gExbidv ph (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv x) B) ch) x
      (by
        aesop)
      hyp_rexbidv2_1
  have p0001 := (Nominal.biimpRefl (synWrex x A ps))
  have p0002 := (Nominal.biimpRefl (synWrex x B ch))
  have p0003 :=
    @gN3bitr4g ph (synWex x (synWa (.classMem (.cv x) A) ps))
      (synWex x (synWa (.classMem (.cv x) B) ch)) (synWrex x A ps) (synWrex x B ch)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ralbii`. -/
@[expose]
noncomputable def gRalbii (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWral x A ph) (synWral x A ps)) :=
  by
  have p0000 := @gA1i (synWb ph ps) synWtru hyp_ralbii_1
  have p0001 :=
    @gRalbidv synWtru ph ps x A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @gTrud (synWb (synWral x A ph) (synWral x A ps)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexbii`. -/
@[expose]
noncomputable def gRexbii (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWrex x A ph) (synWrex x A ps)) :=
  by
  have p0000 := @gA1i (synWb ph ps) synWtru hyp_ralbii_1
  have p0001 :=
    @gRexbidv synWtru ph ps x A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @gTrud (synWb (synWrex x A ph) (synWrex x A ps)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_2ralbii`. -/
@[expose]
noncomputable def gN2ralbii (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (hyp_ralbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B ph)) (synWral x A (synWral y B ps))) :=
  by
  have p0000 := @gRalbii ph ps y B hyp_ralbii_1
  have p0001 := @gRalbii (synWral y B ph) (synWral y B ps) x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2rexbii`. -/
@[expose]
noncomputable def gN2rexbii (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (hyp_ralbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf
      (synWb (synWrex x A (synWrex y B ph)) (synWrex x A (synWrex y B ps))) :=
  by
  have p0000 := @gRexbii ph ps y B hyp_ralbii_1
  have p0001 := @gRexbii (synWrex y B ph) (synWrex y B ps) x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralbii2`. -/
@[expose]
noncomputable def gRalbii2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_ralbii2_1 : Nominal.NPrf
        (synWb (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ps))) :
    Nominal.NPrf (synWb (synWral x A ph) (synWral x B ps)) :=
  by
  have p0000 :=
    @gAlbii (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ps) x
      hyp_ralbii2_1
  have p0001 := (Nominal.biimpRefl (synWral x A ph))
  have p0002 := (Nominal.biimpRefl (synWral x B ps))
  have p0003 :=
    @gN3bitr4i (.all x (.imp (.classMem (.cv x) A) ph))
      (.all x (.imp (.classMem (.cv x) B) ps)) (synWral x A ph) (synWral x B ps) p0000
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_rexbii2`. -/
@[expose]
noncomputable def gRexbii2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_rexbii2_1 : Nominal.NPrf
        (synWb (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) ps))) :
    Nominal.NPrf (synWb (synWrex x A ph) (synWrex x B ps)) :=
  by
  have p0000 :=
    @gExbii (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) ps) x
      hyp_rexbii2_1
  have p0001 := (Nominal.biimpRefl (synWrex x A ph))
  have p0002 := (Nominal.biimpRefl (synWrex x B ps))
  have p0003 :=
    @gN3bitr4i (synWex x (synWa (.classMem (.cv x) A) ph))
      (synWex x (synWa (.classMem (.cv x) B) ps)) (synWrex x A ph) (synWrex x B ps)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ralbiia`. -/
@[expose]
noncomputable def gRalbiia (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralbiia_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWral x A ph) (synWral x A ps)) :=
  by
  have p0000 := @gPm574i (.classMem (.cv x) A) ph ps hyp_ralbiia_1
  have p0001 := @gRalbii2 ph ps x A A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexbiia`. -/
@[expose]
noncomputable def gRexbiia (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralbiia_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWrex x A ph) (synWrex x A ps)) :=
  by
  have p0000 := @gPm532i (.classMem (.cv x) A) ph ps hyp_ralbiia_1
  have p0001 := @gRexbii2 ph ps x A A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r2alf`. -/
@[expose]
noncomputable def gR2alf (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (hyp_r2alf_1 : Nominal.NPrf (synWnfc y A)) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B ph)) (.all x
          (.all y (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x A (synWral y B ph)))
  have p0001 :=
    @gNfcri y x A
      (by
        aesop)
      hyp_r2alf_1
  have p0002 := @gN1921 (.classMem (.cv x) A) (.imp (.classMem (.cv y) B) ph) y p0001
  have p0003 := @gImpexp (.classMem (.cv x) A) (.classMem (.cv y) B) ph
  have p0004 :=
    @gAlbii (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)
      (.imp (.classMem (.cv x) A) (.imp (.classMem (.cv y) B) ph)) y p0003
  have p0005 := (Nominal.biimpRefl (synWral y B ph))
  have p0006 :=
    @gImbi2i (synWral y B ph) (.all y (.imp (.classMem (.cv y) B) ph))
      (.classMem (.cv x) A) p0005
  have p0007 :=
    @gN3bitr4i (.all y (.imp (.classMem (.cv x) A) (.imp (.classMem (.cv y) B) ph)))
      (.imp (.classMem (.cv x) A) (.all y (.imp (.classMem (.cv y) B) ph)))
      (.all y (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph))
      (.imp (.classMem (.cv x) A) (synWral y B ph)) p0002 p0004 p0006
  have p0008 :=
    @gAlbii (.all y (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph))
      (.imp (.classMem (.cv x) A) (synWral y B ph)) x p0007
  have p0009 :=
    @gBitr4i (synWral x A (synWral y B ph))
      (.all x (.imp (.classMem (.cv x) A) (synWral y B ph)))
      (.all x (.all y (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_r2exf`. -/
@[expose]
noncomputable def gR2exf (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (hyp_r2alf_1 : Nominal.NPrf (synWnfc y A)) :
    Nominal.NPrf
      (synWb (synWrex x A (synWrex y B ph)) (synWex x (synWex y
            (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWrex x A (synWrex y B ph)))
  have p0001 :=
    @gNfcri y x A
      (by
        aesop)
      hyp_r2alf_1
  have p0002 := @gN1942 (.classMem (.cv x) A) (synWa (.classMem (.cv y) B) ph) y p0001
  have p0003 := @gAnass (.classMem (.cv x) A) (.classMem (.cv y) B) ph
  have p0004 :=
    @gExbii (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)
      (synWa (.classMem (.cv x) A) (synWa (.classMem (.cv y) B) ph)) y p0003
  have p0005 := (Nominal.biimpRefl (synWrex y B ph))
  have p0006 :=
    @gAnbi2i (synWrex y B ph) (synWex y (synWa (.classMem (.cv y) B) ph))
      (.classMem (.cv x) A) p0005
  have p0007 :=
    @gN3bitr4i
      (synWex y (synWa (.classMem (.cv x) A) (synWa (.classMem (.cv y) B) ph)))
      (synWa (.classMem (.cv x) A) (synWex y (synWa (.classMem (.cv y) B) ph)))
      (synWex y (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph))
      (synWa (.classMem (.cv x) A) (synWrex y B ph)) p0002 p0004 p0006
  have p0008 :=
    @gExbii (synWex y (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph))
      (synWa (.classMem (.cv x) A) (synWrex y B ph)) x p0007
  have p0009 :=
    @gBitr4i (synWrex x A (synWrex y B ph))
      (synWex x (synWa (.classMem (.cv x) A) (synWrex y B ph)))
      (synWex x (synWex y (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_r2al`. -/
@[expose]
noncomputable def gR2al (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B ph)) (.all x
          (.all y (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))) :=
  by
  have p0000 :=
    @gNfcv y A
      (by
        aesop)
  have p0001 :=
    @gR2alf ph x y A B
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r2ex`. -/
@[expose]
noncomputable def gR2ex (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWrex x A (synWrex y B ph)) (synWex x (synWex y
            (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))) :=
  by
  have p0000 :=
    @gNfcv y A
      (by
        aesop)
  have p0001 :=
    @gR2exf ph x y A B
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2ralbidv`. -/
@[expose]
noncomputable def gN2ralbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2ralbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf
      (.imp ph (synWb (synWral x A (synWral y B ps)) (synWral x A (synWral y B ch)))) :=
  by
  have p0000 :=
    @gRalbidv ph ps ch y B
      (by
        aesop)
      hyp_n_2ralbidv_1
  have p0001 :=
    @gRalbidv ph (synWral y B ps) (synWral y B ch) x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2rexbidv`. -/
@[expose]
noncomputable def gN2rexbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2ralbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf
      (.imp ph (synWb (synWrex x A (synWrex y B ps)) (synWrex x A (synWrex y B ch)))) :=
  by
  have p0000 :=
    @gRexbidv ph ps ch y B
      (by
        aesop)
      hyp_n_2ralbidv_1
  have p0001 :=
    @gRexbidv ph (synWrex y B ps) (synWrex y B ch) x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexralbidv`. -/
@[expose]
noncomputable def gRexralbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2ralbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf
      (.imp ph (synWb (synWrex x A (synWral y B ps)) (synWrex x A (synWral y B ch)))) :=
  by
  have p0000 :=
    @gRalbidv ph ps ch y B
      (by
        aesop)
      hyp_n_2ralbidv_1
  have p0001 :=
    @gRexbidv ph (synWral y B ps) (synWral y B ch) x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexanali`. -/
@[expose]
noncomputable def gRexanali (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWrex x A (synWa ph (.neg ps))) (.neg (synWral x A (.imp ph ps)))) :=
  by
  have p0000 := @gAnnim ph ps
  have p0001 := @gRexbii (synWa ph (.neg ps)) (.neg (.imp ph ps)) x A p0000
  have p0002 := @gRexnal (.imp ph ps) x A
  have p0003 :=
    @gBitri (synWrex x A (synWa ph (.neg ps))) (synWrex x A (.neg (.imp ph ps)))
      (.neg (synWral x A (.imp ph ps))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_risset`. -/
@[expose]
noncomputable def gRisset (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (synWb (.classMem A B) (synWrex x B (.classEq (.cv x) A))) :=
  by
  have p0000 := @gExancom (.classMem (.cv x) B) (.classEq (.cv x) A) x
  have p0001 := (Nominal.biimpRefl (synWrex x B (.classEq (.cv x) A)))
  have p0002 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A B (by
        aesop) (by
        aesop))
  have p0003 :=
    @gN3bitr4ri (synWex x (synWa (.classMem (.cv x) B) (.classEq (.cv x) A)))
      (synWex x (synWa (.classEq (.cv x) A) (.classMem (.cv x) B)))
      (synWrex x B (.classEq (.cv x) A)) (.classMem A B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfra1`. -/
@[expose]
noncomputable def gNfra1 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (synWnf x (synWral x A ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x A ph))
  have p0001 := @gNfa1 (.imp (.classMem (.cv x) A) ph) x
  have p0002 :=
    @gNfxfr (synWral x A ph) (.all x (.imp (.classMem (.cv x) A) ph)) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfrald`. -/
@[expose]
noncomputable def gNfrald (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_nfrald_2 : Nominal.NPrf (synWnf y ph))
    (hyp_nfrald_3 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_nfrald_4 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (synWral y A ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral y A ps))
  have p0001 := @gNfcvf x y
  have p0002 :=
    @gAdantl (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnfc x (.cv y)) ph p0001
  have p0003 :=
    @gAdantr ph (synWnfc x A) (.neg (.all x (.classEq (.cv x) (.cv y)))) hyp_nfrald_3
  have p0004 :=
    @gNfeld (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) x (.cv y) A p0002
      p0003
  have p0005 :=
    @gAdantr ph (synWnf x ps) (.neg (.all x (.classEq (.cv x) (.cv y)))) hyp_nfrald_4
  have p0006 :=
    @gNfimd (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) (.classMem (.cv y) A)
      ps x p0004 p0005
  have p0007_e01_recanon :
    Nominal.NPrf
      (.imp (synWa ph (.neg (.all x (.objEq x y))))
        (synWnf x (.imp (.classMem (.cv y) A) ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWnf
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
    @gNfald2 ph (.imp (.classMem (.cv y) A) ps) x y hyp_nfrald_2 p0007_e01_recanon
  have p0008 :=
    @gNfxfrd (synWral y A ps) (.all y (.imp (.classMem (.cv y) A) ps)) ph x p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_nfral`. -/
@[expose]
noncomputable def gNfral (ph : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_nfral_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfral_2 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWnf x (synWral y A ph)) :=
  by
  have p0000 := @gNftru y
  have p0001 := @gA1i (synWnfc x A) synWtru hyp_nfral_1
  have p0002 := @gA1i (synWnf x ph) synWtru hyp_nfral_2
  have p0003 := @gNfrald synWtru ph x y A p0000 p0001 p0002
  have p0004 := @gTrud (synWnf x (synWral y A ph)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfra2`. -/
@[expose]
noncomputable def gNfra2 (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) : Nominal.NPrf (synWnf y (synWral x A (synWral y B ph))) :=
  by
  have p0000 :=
    @gNfcv y A
      (by
        aesop)
  have p0001 := @gNfra1 ph y B
  have p0002 := @gNfral (synWral y B ph) y x A p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfrex`. -/
@[expose]
noncomputable def gNfrex (ph : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_nfrex_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfrex_2 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWnf x (synWrex y A ph)) :=
  by
  have p0000 := @gDfrex2 ph y A
  have p0001 := @gNfn ph x hyp_nfrex_2
  have p0002 := @gNfral (.neg ph) x y A hyp_nfrex_1 p0001
  have p0003 := @gNfn (synWral y A (.neg ph)) x p0002
  have p0004 := @gNfxfr (synWrex y A ph) (.neg (synWral y A (.neg ph))) x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfre1`. -/
@[expose]
noncomputable def gNfre1 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (synWnf x (synWrex x A ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWrex x A ph))
  have p0001 := @gNfe1 (synWa (.classMem (.cv x) A) ph) x
  have p0002 :=
    @gNfxfr (synWrex x A ph) (synWex x (synWa (.classMem (.cv x) A) ph)) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexex`. -/
@[expose]
noncomputable def gRexex (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (synWrex x A ph) (synWex x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWrex x A ph))
  have p0001 := @gSimpr (.classMem (.cv x) A) ph
  have p0002 := @gEximi (synWa (.classMem (.cv x) A) ph) ph x p0001
  have p0003 :=
    @gSylbi (synWrex x A ph) (synWex x (synWa (.classMem (.cv x) A) ph))
      (synWex x ph) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_rsp`. -/
@[expose]
noncomputable def gRsp (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (synWral x A ph) (.imp (.classMem (.cv x) A) ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x A ph))
  have p0001 := @gSp (.imp (.classMem (.cv x) A) ph) x
  have p0002 :=
    @gSylbi (synWral x A ph) (.all x (.imp (.classMem (.cv x) A) ph))
      (.imp (.classMem (.cv x) A) ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rspe`. -/
@[expose]
noncomputable def gRspe (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (synWa (.classMem (.cv x) A) ph) (synWrex x A ph)) :=
  by
  have p0000 := @gN198a (synWa (.classMem (.cv x) A) ph) x
  have p0001 := (Nominal.biimpRefl (synWrex x A ph))
  have p0002 :=
    @gSylibr (synWa (.classMem (.cv x) A) ph)
      (synWex x (synWa (.classMem (.cv x) A) ph)) (synWrex x A ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rsp2`. -/
@[expose]
noncomputable def gRsp2 (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWral x A (synWral y B ph))
        (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)) :=
  by
  have p0000 := @gRsp (synWral y B ph) x A
  have p0001 := @gRsp ph y B
  have p0002 :=
    @gSyl6 (synWral x A (synWral y B ph)) (.classMem (.cv x) A) (synWral y B ph)
      (.imp (.classMem (.cv y) B) ph) p0000 p0001
  have p0003 :=
    @gImp3a (synWral x A (synWral y B ph)) (.classMem (.cv x) A) (.classMem (.cv y) B)
      ph p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_rgen`. -/
@[expose]
noncomputable def gRgen (ph : Wff) (x : Var) (A : Class)
    (hyp_rgen_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) ph)) :
    Nominal.NPrf (synWral x A ph) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x A ph))
  have p0001 :=
    @gMpgbir (synWral x A ph) (.imp (.classMem (.cv x) A) ph) x p0000 hyp_rgen_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rgen2a`. -/
@[expose]
noncomputable def gRgen2a (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (hyp_rgen2a_1 :
      Nominal.NPrf (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) ph)) :
    Nominal.NPrf (synWral x A (synWral y A ph)) :=
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
  have p0000 := @gEleq1 (.cv y) (.cv x) A
  have p0001 := @gEx (.classMem (.cv x) A) (.classMem (.cv y) A) ph hyp_rgen2a_1
  have p0002 :=
    @gSyl6bi (.classEq (.cv y) (.cv x)) (.classMem (.cv y) A) (.classMem (.cv x) A)
      (.imp (.classMem (.cv y) A) ph) p0000 p0001
  have p0003 := @gPm243d (.classEq (.cv y) (.cv x)) (.classMem (.cv y) A) ph p0002
  have p0004 :=
    @gAlimi (.classEq (.cv y) (.cv x)) (.imp (.classMem (.cv y) A) ph) y p0003
  have p0005 :=
    @gA1d (.all y (.classEq (.cv y) (.cv x))) (.all y (.imp (.classMem (.cv y) A) ph))
      (.classMem (.cv x) A) p0004
  have p0006 := @gEleq1 (.cv z) (.cv x) A
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (synWb (.classMem (.cv z) A) (.classMem (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gDvelimv (.classMem (.cv z) A) (.classMem (.cv x) A) y x z
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      (by
        aesop)
      p0007_e00_recanon
  have p0008 := @gAlimi (.classMem (.cv x) A) (.imp (.classMem (.cv y) A) ph) y p0001
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
    @gSyl6 (.neg (.all y (.classEq (.cv y) (.cv x)))) (.classMem (.cv x) A)
      (.all y (.classMem (.cv x) A)) (.all y (.imp (.classMem (.cv y) A) ph))
      p0009_e00_recanon p0008
  have p0010 :=
    @gPm261i (.all y (.classEq (.cv y) (.cv x)))
      (.imp (.classMem (.cv x) A) (.all y (.imp (.classMem (.cv y) A) ph))) p0005 p0009
  have p0011 := (Nominal.biimpRefl (synWral y A ph))
  have p0012 :=
    @gSylibr (.classMem (.cv x) A) (.all y (.imp (.classMem (.cv y) A) ph))
      (synWral y A ph) p0010 p0011
  have p0013 := @gRgen (synWral y A ph) x A p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_rgenw`. -/
@[expose]
noncomputable def gRgenw (ph : Wff) (x : Var) (A : Class)
    (hyp_rgenw_1 : Nominal.NPrf ph) : Nominal.NPrf (synWral x A ph) :=
  by
  have p0000 := @gA1i ph (.classMem (.cv x) A) hyp_rgenw_1
  have p0001 := @gRgen ph x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rgen2w`. -/
@[expose]
noncomputable def gRgen2w (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_rgenw_1 : Nominal.NPrf ph) : Nominal.NPrf (synWral x A (synWral y B ph)) :=
  by
  have p0000 := @gRgenw ph y B hyp_rgenw_1
  have p0001 := @gRgenw (synWral y B ph) x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mprg`. -/
@[expose]
noncomputable def gMprg (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_mprg_1 : Nominal.NPrf (.imp (synWral x A ph) ps))
    (hyp_mprg_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) ph)) : Nominal.NPrf ps :=
  by
  have p0000 := @gRgen ph x A hyp_mprg_2
  have p0001 := Nominal.mp p0000 hyp_mprg_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mprgbir`. -/
@[expose]
noncomputable def gMprgbir (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_mprgbir_1 : Nominal.NPrf (synWb ph (synWral x A ps)))
    (hyp_mprgbir_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) ps)) : Nominal.NPrf ph :=
  by
  have p0000 := @gRgen ps x A hyp_mprgbir_2
  have p0001 := @gMpbir ph (synWral x A ps) p0000 hyp_mprgbir_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralim`. -/
@[expose]
noncomputable def gRalim (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (synWral x A (.imp ph ps)) (.imp (synWral x A ph) (synWral x A ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x A (.imp ph ps)))
  have p0001 := Nominal.ax2 (.classMem (.cv x) A) ph ps
  have p0002 :=
    @gAl2imi (.imp (.classMem (.cv x) A) (.imp ph ps)) (.imp (.classMem (.cv x) A) ph)
      (.imp (.classMem (.cv x) A) ps) x p0001
  have p0003 :=
    @gSylbi (synWral x A (.imp ph ps))
      (.all x (.imp (.classMem (.cv x) A) (.imp ph ps)))
      (.imp (.all x (.imp (.classMem (.cv x) A) ph)) (.all x (.imp (.classMem (.cv x) A) ps)))
      p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWral x A ph))
  have p0005 := (Nominal.biimpRefl (synWral x A ps))
  have p0006 :=
    @gN3imtr4g (synWral x A (.imp ph ps)) (.all x (.imp (.classMem (.cv x) A) ph))
      (.all x (.imp (.classMem (.cv x) A) ps)) (synWral x A ph) (synWral x A ps) p0003
      p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ralimi2`. -/
@[expose]
noncomputable def gRalimi2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_ralimi2_1 : Nominal.NPrf
        (.imp (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ps))) :
    Nominal.NPrf (.imp (synWral x A ph) (synWral x B ps)) :=
  by
  have p0000 :=
    @gAlimi (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ps) x
      hyp_ralimi2_1
  have p0001 := (Nominal.biimpRefl (synWral x A ph))
  have p0002 := (Nominal.biimpRefl (synWral x B ps))
  have p0003 :=
    @gN3imtr4i (.all x (.imp (.classMem (.cv x) A) ph))
      (.all x (.imp (.classMem (.cv x) B) ps)) (synWral x A ph) (synWral x B ps) p0000
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ralimia`. -/
@[expose]
noncomputable def gRalimia (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralimia_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.imp ph ps))) :
    Nominal.NPrf (.imp (synWral x A ph) (synWral x A ps)) :=
  by
  have p0000 := @gA2i (.classMem (.cv x) A) ph ps hyp_ralimia_1
  have p0001 := @gRalimi2 ph ps x A A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralimiaa`. -/
@[expose]
noncomputable def gRalimiaa (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralimiaa_1 : Nominal.NPrf (.imp (synWa (.classMem (.cv x) A) ph) ps)) :
    Nominal.NPrf (.imp (synWral x A ph) (synWral x A ps)) :=
  by
  have p0000 := @gEx (.classMem (.cv x) A) ph ps hyp_ralimiaa_1
  have p0001 := @gRalimia ph ps x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralimi`. -/
@[expose]
noncomputable def gRalimi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralimi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWral x A ph) (synWral x A ps)) :=
  by
  have p0000 := @gA1i (.imp ph ps) (.classMem (.cv x) A) hyp_ralimi_1
  have p0001 := @gRalimia ph ps x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ral2imi`. -/
@[expose]
noncomputable def gRal2imi (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ral2imi_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (synWral x A ph) (.imp (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 := @gRalimi ph (.imp ps ch) x A hyp_ral2imi_1
  have p0001 := @gRalim ps ch x A
  have p0002 :=
    @gSyl (synWral x A ph) (synWral x A (.imp ps ch))
      (.imp (synWral x A ps) (synWral x A ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ralimdaa`. -/
@[expose]
noncomputable def gRalimdaa (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralimdaa_1 : Nominal.NPrf (synWnf x ph))
    (hyp_ralimdaa_2 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 := @gEx ph (.classMem (.cv x) A) (.imp ps ch) hyp_ralimdaa_2
  have p0001 := @gA2d ph (.classMem (.cv x) A) ps ch p0000
  have p0002 :=
    @gAlimd ph (.imp (.classMem (.cv x) A) ps) (.imp (.classMem (.cv x) A) ch) x
      hyp_ralimdaa_1 p0001
  have p0003 := (Nominal.biimpRefl (synWral x A ps))
  have p0004 := (Nominal.biimpRefl (synWral x A ch))
  have p0005 :=
    @gN3imtr4g ph (.all x (.imp (.classMem (.cv x) A) ps))
      (.all x (.imp (.classMem (.cv x) A) ch)) (synWral x A ps) (synWral x A ch) p0002
      p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ralimdva`. -/
@[expose]
noncomputable def gRalimdva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralimdva_1 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gRalimdaa ph ps ch x A p0000 hyp_ralimdva_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralimdv`. -/
@[expose]
noncomputable def gRalimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 := @gAdantr ph (.imp ps ch) (.classMem (.cv x) A) hyp_ralimdv_1
  have p0001 :=
    @gRalimdva ph ps ch x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralrimi`. -/
@[expose]
noncomputable def gRalrimi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_ralrimi_1 : Nominal.NPrf (synWnf x ph))
    (hyp_ralrimi_2 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) ps))) :
    Nominal.NPrf (.imp ph (synWral x A ps)) :=
  by
  have p0000 := @gAlrimi ph (.imp (.classMem (.cv x) A) ps) x hyp_ralrimi_1 hyp_ralrimi_2
  have p0001 := (Nominal.biimpRefl (synWral x A ps))
  have p0002 :=
    @gSylibr ph (.all x (.imp (.classMem (.cv x) A) ps)) (synWral x A ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ralrimiv`. -/
@[expose]
noncomputable def gRalrimiv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralrimiv_1 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) ps))) :
    Nominal.NPrf (.imp ph (synWral x A ps)) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gRalrimi ph ps x A p0000 hyp_ralrimiv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralrimiva`. -/
@[expose]
noncomputable def gRalrimiva (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_ralrimiva_1 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) ps)) :
    Nominal.NPrf (.imp ph (synWral x A ps)) :=
  by
  have p0000 := @gEx ph (.classMem (.cv x) A) ps hyp_ralrimiva_1
  have p0001 :=
    @gRalrimiv ph ps x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralrimivw`. -/
@[expose]
noncomputable def gRalrimivw (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralrimivw_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp ph (synWral x A ps)) :=
  by
  have p0000 := @gA1d ph ps (.classMem (.cv x) A) hyp_ralrimivw_1
  have p0001 :=
    @gRalrimiv ph ps x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r19_21t`. -/
@[expose]
noncomputable def gR1921t (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (synWnf x ph) (synWb (synWral x A (.imp ph ps)) (.imp ph (synWral x A ps)))) :=
  by
  have p0000 := @gBi204 (.classMem (.cv x) A) ph ps
  have p0001 :=
    @gAlbii (.imp (.classMem (.cv x) A) (.imp ph ps))
      (.imp ph (.imp (.classMem (.cv x) A) ps)) x p0000
  have p0002 := @gN1921t ph (.imp (.classMem (.cv x) A) ps) x
  have p0003 :=
    @gSyl5bb (.all x (.imp (.classMem (.cv x) A) (.imp ph ps)))
      (.all x (.imp ph (.imp (.classMem (.cv x) A) ps))) (synWnf x ph)
      (.imp ph (.all x (.imp (.classMem (.cv x) A) ps))) p0001 p0002
  have p0004 := (Nominal.biimpRefl (synWral x A (.imp ph ps)))
  have p0005 := (Nominal.biimpRefl (synWral x A ps))
  have p0006 :=
    @gImbi2i (synWral x A ps) (.all x (.imp (.classMem (.cv x) A) ps)) ph p0005
  have p0007 :=
    @gN3bitr4g (synWnf x ph) (.all x (.imp (.classMem (.cv x) A) (.imp ph ps)))
      (.imp ph (.all x (.imp (.classMem (.cv x) A) ps))) (synWral x A (.imp ph ps))
      (.imp ph (synWral x A ps)) p0003 p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_r19_21`. -/
@[expose]
noncomputable def gR1921 (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_r19_21_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (synWral x A (.imp ph ps)) (.imp ph (synWral x A ps))) :=
  by
  have p0000 := @gR1921t ph ps x A
  have p0001 := Nominal.mp hyp_r19_21_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r19_21v`. -/
@[expose]
noncomputable def gR1921v (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWb (synWral x A (.imp ph ps)) (.imp ph (synWral x A ps))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gR1921 ph ps x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralrimd`. -/
@[expose]
noncomputable def gRalrimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralrimd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_ralrimd_2 : Nominal.NPrf (synWnf x ps))
    (hyp_ralrimd_3 : Nominal.NPrf (.imp ph (.imp ps (.imp (.classMem (.cv x) A) ch)))) :
    Nominal.NPrf (.imp ph (.imp ps (synWral x A ch))) :=
  by
  have p0000 :=
    @gAlrimd ph ps (.imp (.classMem (.cv x) A) ch) x hyp_ralrimd_1 hyp_ralrimd_2
      hyp_ralrimd_3
  have p0001 := (Nominal.biimpRefl (synWral x A ch))
  have p0002 :=
    @gSyl6ibr ph ps (.all x (.imp (.classMem (.cv x) A) ch)) (synWral x A ch) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ralrimdv`. -/
@[expose]
noncomputable def gRalrimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ralrimdv_1 : Nominal.NPrf (.imp ph (.imp ps (.imp (.classMem (.cv x) A) ch)))) :
    Nominal.NPrf (.imp ph (.imp ps (synWral x A ch))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 :=
    @gNfv ps x
      (by
        aesop)
  have p0002 := @gRalrimd ph ps ch x A p0000 p0001 hyp_ralrimdv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ralrimivv`. -/
@[expose]
noncomputable def gRalrimivv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y)
    (hyp_ralrimivv_1 : Nominal.NPrf
        (.imp ph (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ps))) :
    Nominal.NPrf (.imp ph (synWral x A (synWral y B ps))) :=
  by
  have p0000 := @gExp3a ph (.classMem (.cv x) A) (.classMem (.cv y) B) ps hyp_ralrimivv_1
  have p0001 :=
    @gRalrimdv ph (.classMem (.cv x) A) ps y B
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0000
  have p0002 :=
    @gRalrimiv ph (synWral y B ps) x A
      (by
        aesop)
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ralrimivva`. -/
@[expose]
noncomputable def gRalrimivva (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y)
    (hyp_ralrimivva_1 : Nominal.NPrf
        (.imp (synWa ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))) ps)) :
    Nominal.NPrf (.imp ph (synWral x A (synWral y B ps))) :=
  by
  have p0000 :=
    @gEx ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ps hyp_ralrimivva_1
  have p0001 :=
    @gRalrimivv ph ps x y A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ralrimdvv`. -/
@[expose]
noncomputable def gRalrimdvv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralrimdvv_1 : Nominal.NPrf (.imp ph
          (.imp ps (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ch)))) :
    Nominal.NPrf (.imp ph (.imp ps (synWral x A (synWral y B ch)))) :=
  by
  have p0000 :=
    @gImp ph ps (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ch)
      hyp_ralrimdvv_1
  have p0001 :=
    @gRalrimivv (synWa ph ps) ch x y A B
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        aesop)
      p0000
  have p0002 := @gEx ph ps (synWral x A (synWral y B ch)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rgen2`. -/
@[expose]
noncomputable def gRgen2 (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_rgen2_1 :
      Nominal.NPrf (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)) :
    Nominal.NPrf (synWral x A (synWral y B ph)) :=
  by
  have p0000 :=
    @gRalrimiva (.classMem (.cv x) A) ph y B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      hyp_rgen2_1
  have p0001 := @gRgen (synWral y B ph) x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r19_21bi`. -/
@[expose]
noncomputable def gR1921bi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_r19_21bi_1 : Nominal.NPrf (.imp ph (synWral x A ps))) :
    Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) ps) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x A ps))
  have p0001 :=
    @gSylib ph (synWral x A ps) (.all x (.imp (.classMem (.cv x) A) ps)) hyp_r19_21bi_1
      p0000
  have p0002 := @gN1921bi ph (.imp (.classMem (.cv x) A) ps) x p0001
  have p0003 := @gImp ph (.classMem (.cv x) A) ps p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nrex`. -/
@[expose]
noncomputable def gNrex (ps : Wff) (x : Var) (A : Class)
    (hyp_nrex_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.neg ps))) :
    Nominal.NPrf (.neg (synWrex x A ps)) :=
  by
  have p0000 := @gRgen (.neg ps) x A hyp_nrex_1
  have p0001 := @gRalnex ps x A
  have p0002 := @gMpbi (synWral x A (.neg ps)) (.neg (synWrex x A ps)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nrexdv`. -/
@[expose]
noncomputable def gNrexdv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_nrexdv_1 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (synWrex x A ps))) :=
  by
  have p0000 :=
    @gRalrimiva ph (.neg ps) x A
      (by
        aesop)
      hyp_nrexdv_1
  have p0001 := @gRalnex ps x A
  have p0002 := @gSylib ph (synWral x A (.neg ps)) (.neg (synWrex x A ps)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexim`. -/
@[expose]
noncomputable def gRexim (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (synWral x A (.imp ph ps)) (.imp (synWrex x A ph) (synWrex x A ps))) :=
  by
  have p0000 := @gCon3 ph ps
  have p0001 := @gRal2imi (.imp ph ps) (.neg ps) (.neg ph) x A p0000
  have p0002 :=
    @gCon3d (synWral x A (.imp ph ps)) (synWral x A (.neg ps)) (synWral x A (.neg ph))
      p0001
  have p0003 := @gDfrex2 ph x A
  have p0004 := @gDfrex2 ps x A
  have p0005 :=
    @gN3imtr4g (synWral x A (.imp ph ps)) (.neg (synWral x A (.neg ph)))
      (.neg (synWral x A (.neg ps))) (synWrex x A ph) (synWrex x A ps) p0002 p0003
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_reximia`. -/
@[expose]
noncomputable def gReximia (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_reximia_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.imp ph ps))) :
    Nominal.NPrf (.imp (synWrex x A ph) (synWrex x A ps)) :=
  by
  have p0000 := @gRexim ph ps x A
  have p0001 :=
    @gMprg (.imp ph ps) (.imp (synWrex x A ph) (synWrex x A ps)) x A p0000
      hyp_reximia_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_reximi`. -/
@[expose]
noncomputable def gReximi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_reximi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWrex x A ph) (synWrex x A ps)) :=
  by
  have p0000 := @gA1i (.imp ph ps) (.classMem (.cv x) A) hyp_reximi_1
  have p0001 := @gReximia ph ps x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_reximdai`. -/
@[expose]
noncomputable def gReximdai (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_reximdai_1 : Nominal.NPrf (synWnf x ph))
    (hyp_reximdai_2 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 := @gRalrimi ph (.imp ps ch) x A hyp_reximdai_1 hyp_reximdai_2
  have p0001 := @gRexim ps ch x A
  have p0002 :=
    @gSyl ph (synWral x A (.imp ps ch)) (.imp (synWrex x A ps) (synWrex x A ch)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_reximdvai`. -/
@[expose]
noncomputable def gReximdvai (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_reximdvai_1 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gReximdai ph ps ch x A p0000 hyp_reximdvai_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_reximdv`. -/
@[expose]
noncomputable def gReximdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_reximdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 := @gA1d ph (.imp ps ch) (.classMem (.cv x) A) hyp_reximdv_1
  have p0001 :=
    @gReximdvai ph ps ch x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_reximdva`. -/
@[expose]
noncomputable def gReximdva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_reximdva_1 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 := @gEx ph (.classMem (.cv x) A) (.imp ps ch) hyp_reximdva_1
  have p0001 :=
    @gReximdvai ph ps ch x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r19_23t`. -/
@[expose]
noncomputable def gR1923t (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (synWnf x ps) (synWb (synWral x A (.imp ph ps)) (.imp (synWrex x A ph) ps))) :=
  by
  have p0000 := @gN1923t (synWa (.classMem (.cv x) A) ph) ps x
  have p0001 := (Nominal.biimpRefl (synWral x A (.imp ph ps)))
  have p0002 := @gImpexp (.classMem (.cv x) A) ph ps
  have p0003 :=
    @gAlbii (.imp (synWa (.classMem (.cv x) A) ph) ps)
      (.imp (.classMem (.cv x) A) (.imp ph ps)) x p0002
  have p0004 :=
    @gBitr4i (synWral x A (.imp ph ps))
      (.all x (.imp (.classMem (.cv x) A) (.imp ph ps)))
      (.all x (.imp (synWa (.classMem (.cv x) A) ph) ps)) p0001 p0003
  have p0005 := (Nominal.biimpRefl (synWrex x A ph))
  have p0006 :=
    @gImbi1i (synWrex x A ph) (synWex x (synWa (.classMem (.cv x) A) ph)) ps p0005
  have p0007 :=
    @gN3bitr4g (synWnf x ps) (.all x (.imp (synWa (.classMem (.cv x) A) ph) ps))
      (.imp (synWex x (synWa (.classMem (.cv x) A) ph)) ps) (synWral x A (.imp ph ps))
      (.imp (synWrex x A ph) ps) p0000 p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_r19_23`. -/
@[expose]
noncomputable def gR1923 (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_r19_23_1 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWb (synWral x A (.imp ph ps)) (.imp (synWrex x A ph) ps)) :=
  by
  have p0000 := @gR1923t ph ps x A
  have p0001 := Nominal.mp hyp_r19_23_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r19_23v`. -/
@[expose]
noncomputable def gR1923v (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (synWb (synWral x A (.imp ph ps)) (.imp (synWrex x A ph) ps)) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 := @gR1923 ph ps x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimi`. -/
@[expose]
noncomputable def gRexlimi (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_rexlimi_1 : Nominal.NPrf (synWnf x ps))
    (hyp_rexlimi_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.imp ph ps))) :
    Nominal.NPrf (.imp (synWrex x A ph) ps) :=
  by
  have p0000 := @gRgen (.imp ph ps) x A hyp_rexlimi_2
  have p0001 := @gR1923 ph ps x A hyp_rexlimi_1
  have p0002 :=
    @gMpbi (synWral x A (.imp ph ps)) (.imp (synWrex x A ph) ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexlimiv`. -/
@[expose]
noncomputable def gRexlimiv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv)
    (hyp_rexlimiv_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.imp ph ps))) :
    Nominal.NPrf (.imp (synWrex x A ph) ps) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 := @gRexlimi ph ps x A p0000 hyp_rexlimiv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimiva`. -/
@[expose]
noncomputable def gRexlimiva (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv)
    (hyp_rexlimiva_1 : Nominal.NPrf (.imp (synWa (.classMem (.cv x) A) ph) ps)) :
    Nominal.NPrf (.imp (synWrex x A ph) ps) :=
  by
  have p0000 := @gEx (.classMem (.cv x) A) ph ps hyp_rexlimiva_1
  have p0001 :=
    @gRexlimiv ph ps x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimivw`. -/
@[expose]
noncomputable def gRexlimivw (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv) (hyp_rexlimivw_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWrex x A ph) ps) :=
  by
  have p0000 := @gA1i (.imp ph ps) (.classMem (.cv x) A) hyp_rexlimivw_1
  have p0001 :=
    @gRexlimiv ph ps x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimd`. -/
@[expose]
noncomputable def gRexlimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_rexlimd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_rexlimd_2 : Nominal.NPrf (synWnf x ch))
    (hyp_rexlimd_3 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) ch)) :=
  by
  have p0000 := @gRalrimi ph (.imp ps ch) x A hyp_rexlimd_1 hyp_rexlimd_3
  have p0001 := @gR1923 ps ch x A hyp_rexlimd_2
  have p0002 :=
    @gSylib ph (synWral x A (.imp ps ch)) (.imp (synWrex x A ps) ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexlimdv`. -/
@[expose]
noncomputable def gRexlimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdv_1 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) ch)) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 :=
    @gNfv ch x
      (by
        aesop)
  have p0002 := @gRexlimd ph ps ch x A p0000 p0001 hyp_rexlimdv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexlimdva`. -/
@[expose]
noncomputable def gRexlimdva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdva_1 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) ch)) :=
  by
  have p0000 := @gEx ph (.classMem (.cv x) A) (.imp ps ch) hyp_rexlimdva_1
  have p0001 :=
    @gRexlimdv ph ps ch x A
      (by
        aesop)
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimdvaa`. -/
@[expose]
noncomputable def gRexlimdvaa (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdvaa_1 : Nominal.NPrf (.imp (synWa ph (synWa (.classMem (.cv x) A) ps)) ch)) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) ch)) :=
  by
  have p0000 := @gExpr ph (.classMem (.cv x) A) ps ch hyp_rexlimdvaa_1
  have p0001 :=
    @gRexlimdva ph ps ch x A
      (by
        aesop)
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimdv3a`. -/
@[expose]
noncomputable def gRexlimdv3a (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdv3a_1 : Nominal.NPrf (.imp (synW3a ph (.classMem (.cv x) A) ps) ch)) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) ch)) :=
  by
  have p0000 := @gN3exp ph (.classMem (.cv x) A) ps ch hyp_rexlimdv3a_1
  have p0001 :=
    @gRexlimdv ph ps ch x A
      (by
        aesop)
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimdvw`. -/
@[expose]
noncomputable def gRexlimdvw (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimdvw_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A ps) ch)) :=
  by
  have p0000 := @gA1d ph (.imp ps ch) (.classMem (.cv x) A) hyp_rexlimdvw_1
  have p0001 :=
    @gRexlimdv ph ps ch x A
      (by
        aesop)
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimddv`. -/
@[expose]
noncomputable def gRexlimddv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_rexlimddv_1 : Nominal.NPrf (.imp ph (synWrex x A ps)))
    (hyp_rexlimddv_2 : Nominal.NPrf (.imp (synWa ph (synWa (.classMem (.cv x) A) ps)) ch)) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 :=
    @gRexlimdvaa ph ps ch x A
      (by
        aesop)
      (by
        aesop)
      hyp_rexlimddv_2
  have p0001 := @gMpd ph (synWrex x A ps) ch hyp_rexlimddv_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimivv`. -/
@[expose]
noncomputable def gRexlimivv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_rexlimivv_1 : Nominal.NPrf
        (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.imp ph ps))) :
    Nominal.NPrf (.imp (synWrex x A (synWrex y B ph)) ps) :=
  by
  have p0000 :=
    @gRexlimdva (.classMem (.cv x) A) ph ps y B
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      hyp_rexlimivv_1
  have p0001 :=
    @gRexlimiv (synWrex y B ph) ps x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexlimdvv`. -/
@[expose]
noncomputable def gRexlimdvv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ch_y : y ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_rexlimdvv_1 : Nominal.NPrf (.imp ph
          (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A (synWrex y B ps)) ch)) :=
  by
  have p0000 :=
    @gExpdimp ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.imp ps ch) hyp_rexlimdvv_1
  have p0001 :=
    @gRexlimdv (synWa ph (.classMem (.cv x) A)) ps ch y B
      (by
        aesop)
      (by
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
    @gRexlimdva ph (synWrex y B ps) ch x A
      (by
        aesop)
      (by
        aesop)
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexlimdvva`. -/
@[expose]
noncomputable def gRexlimdvva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ch_y : y ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_rexlimdvva_1 : Nominal.NPrf
        (.imp (synWa ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWrex x A (synWrex y B ps)) ch)) :=
  by
  have p0000 :=
    @gEx ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.imp ps ch)
      hyp_rexlimdvva_1
  have p0001 :=
    @gRexlimdvv ph ps ch x y A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r19_26`. -/
@[expose]
noncomputable def gR1926 (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWral x A (synWa ph ps)) (synWa (synWral x A ph) (synWral x A ps))) :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := @gRalimi (synWa ph ps) ph x A p0000
  have p0002 := @gSimpr ph ps
  have p0003 := @gRalimi (synWa ph ps) ps x A p0002
  have p0004 :=
    @gJca (synWral x A (synWa ph ps)) (synWral x A ph) (synWral x A ps) p0001 p0003
  have p0005 := @g_pm3_2 ph ps
  have p0006 := @gRal2imi ph ps (synWa ph ps) x A p0005
  have p0007 :=
    @gImp (synWral x A ph) (synWral x A ps) (synWral x A (synWa ph ps)) p0006
  have p0008 :=
    @gImpbii (synWral x A (synWa ph ps)) (synWa (synWral x A ph) (synWral x A ps))
      p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_r19_26_2`. -/
@[expose]
noncomputable def g_r19_26_2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B (synWa ph ps)))
        (synWa (synWral x A (synWral y B ph)) (synWral x A (synWral y B ps)))) :=
  by
  have p0000 := @gR1926 ph ps y B
  have p0001 :=
    @gRalbii (synWral y B (synWa ph ps)) (synWa (synWral y B ph) (synWral y B ps)) x
      A p0000
  have p0002 := @gR1926 (synWral y B ph) (synWral y B ps) x A
  have p0003 :=
    @gBitri (synWral x A (synWral y B (synWa ph ps)))
      (synWral x A (synWa (synWral y B ph) (synWral y B ps)))
      (synWa (synWral x A (synWral y B ph)) (synWral x A (synWral y B ps))) p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ralbiim`. -/
@[expose]
noncomputable def gRalbiim (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWral x A (synWb ph ps))
        (synWa (synWral x A (.imp ph ps)) (synWral x A (.imp ps ph)))) :=
  by
  have p0000 := @gDfbi2 ph ps
  have p0001 := @gRalbii (synWb ph ps) (synWa (.imp ph ps) (.imp ps ph)) x A p0000
  have p0002 := @gR1926 (.imp ph ps) (.imp ps ph) x A
  have p0003 :=
    @gBitri (synWral x A (synWb ph ps))
      (synWral x A (synWa (.imp ph ps) (.imp ps ph)))
      (synWa (synWral x A (.imp ph ps)) (synWral x A (.imp ps ph))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_r19_27av`. -/
@[expose]
noncomputable def gR1927av (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (.imp (synWa (synWral x A ph) ps) (synWral x A (synWa ph ps))) :=
  by
  have p0000 := Nominal.ax1 ps (.classMem (.cv x) A)
  have p0001 :=
    @gRalrimiv ps ps x A
      (by
        aesop)
      p0000
  have p0002 := @gAnim2i ps (synWral x A ps) (synWral x A ph) p0001
  have p0003 := @gR1926 ph ps x A
  have p0004 :=
    @gSylibr (synWa (synWral x A ph) ps) (synWa (synWral x A ph) (synWral x A ps))
      (synWral x A (synWa ph ps)) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_r19_28av`. -/
@[expose]
noncomputable def gR1928av (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.imp (synWa ph (synWral x A ps)) (synWral x A (synWa ph ps))) :=
  by
  have p0000 :=
    @gR1927av ps ph x A
      (by
        aesop)
  have p0001 := @gAncom ph (synWral x A ps)
  have p0002 := @gAncom ph ps
  have p0003 := @gRalbii (synWa ph ps) (synWa ps ph) x A p0002
  have p0004 :=
    @gN3imtr4i (synWa (synWral x A ps) ph) (synWral x A (synWa ps ph))
      (synWa ph (synWral x A ps)) (synWral x A (synWa ph ps)) p0000 p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_r19_29`. -/
@[expose]
noncomputable def gR1929 (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (synWa (synWral x A ph) (synWrex x A ps)) (synWrex x A (synWa ph ps))) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @gRalimi ph (.imp ps (synWa ph ps)) x A p0000
  have p0002 := @gRexim ps (synWa ph ps) x A
  have p0003 :=
    @gSyl (synWral x A ph) (synWral x A (.imp ps (synWa ph ps)))
      (.imp (synWrex x A ps) (synWrex x A (synWa ph ps))) p0001 p0002
  have p0004 :=
    @gImp (synWral x A ph) (synWrex x A ps) (synWrex x A (synWa ph ps)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_r19_35`. -/
@[expose]
noncomputable def gR1935 (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWrex x A (.imp ph ps)) (.imp (synWral x A ph) (synWrex x A ps))) :=
  by
  have p0000 := @gR1926 ph (.neg ps) x A
  have p0001 := @gAnnim ph ps
  have p0002 := @gRalbii (synWa ph (.neg ps)) (.neg (.imp ph ps)) x A p0001
  have p0003 := (Nominal.biimpRefl (synWa (synWral x A ph) (synWral x A (.neg ps))))
  have p0004 :=
    @gN3bitr3i (synWral x A (synWa ph (.neg ps)))
      (synWa (synWral x A ph) (synWral x A (.neg ps)))
      (synWral x A (.neg (.imp ph ps)))
      (.neg (.imp (synWral x A ph) (.neg (synWral x A (.neg ps))))) p0000 p0002 p0003
  have p0005 :=
    @gCon2bii (synWral x A (.neg (.imp ph ps)))
      (.imp (synWral x A ph) (.neg (synWral x A (.neg ps)))) p0004
  have p0006 := @gDfrex2 ps x A
  have p0007 :=
    @gImbi2i (synWrex x A ps) (.neg (synWral x A (.neg ps))) (synWral x A ph) p0006
  have p0008 := @gDfrex2 (.imp ph ps) x A
  have p0009 :=
    @gN3bitr4ri (.imp (synWral x A ph) (.neg (synWral x A (.neg ps))))
      (.neg (synWral x A (.neg (.imp ph ps)))) (.imp (synWral x A ph) (synWrex x A ps))
      (synWrex x A (.imp ph ps)) p0005 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_r19_41`. -/
@[expose]
noncomputable def gR1941 (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_r19_41_1 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWb (synWrex x A (synWa ph ps)) (synWa (synWrex x A ph) ps)) :=
  by
  have p0000 := @gAnass (.classMem (.cv x) A) ph ps
  have p0001 :=
    @gExbii (synWa (synWa (.classMem (.cv x) A) ph) ps)
      (synWa (.classMem (.cv x) A) (synWa ph ps)) x p0000
  have p0002 := @gN1941 (synWa (.classMem (.cv x) A) ph) ps x hyp_r19_41_1
  have p0003 :=
    @gBitr3i (synWex x (synWa (.classMem (.cv x) A) (synWa ph ps)))
      (synWex x (synWa (synWa (.classMem (.cv x) A) ph) ps))
      (synWa (synWex x (synWa (.classMem (.cv x) A) ph)) ps) p0001 p0002
  have p0004 := (Nominal.biimpRefl (synWrex x A (synWa ph ps)))
  have p0005 := (Nominal.biimpRefl (synWrex x A ph))
  have p0006 :=
    @gAnbi1i (synWrex x A ph) (synWex x (synWa (.classMem (.cv x) A) ph)) ps p0005
  have p0007 :=
    @gN3bitr4i (synWex x (synWa (.classMem (.cv x) A) (synWa ph ps)))
      (synWa (synWex x (synWa (.classMem (.cv x) A) ph)) ps)
      (synWrex x A (synWa ph ps)) (synWa (synWrex x A ph) ps) p0003 p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_r19_41v`. -/
@[expose]
noncomputable def gR1941v (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (synWb (synWrex x A (synWa ph ps)) (synWa (synWrex x A ph) ps)) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 := @gR1941 ph ps x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_r19_42v`. -/
@[expose]
noncomputable def gR1942v (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWb (synWrex x A (synWa ph ps)) (synWa ph (synWrex x A ps))) :=
  by
  have p0000 :=
    @gR1941v ps ph x A
      (by
        aesop)
  have p0001 := @gAncom ph ps
  have p0002 := @gRexbii (synWa ph ps) (synWa ps ph) x A p0001
  have p0003 := @gAncom ph (synWrex x A ps)
  have p0004 :=
    @gN3bitr4i (synWrex x A (synWa ps ph)) (synWa (synWrex x A ps) ph)
      (synWrex x A (synWa ph ps)) (synWa ph (synWrex x A ps)) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_r19_43`. -/
@[expose]
noncomputable def gR1943 (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWrex x A (synWo ph ps)) (synWo (synWrex x A ph) (synWrex x A ps))) :=
  by
  have p0000 := @gR1935 (.neg ph) ps x A
  have p0001 := (Nominal.biimpRefl (synWo ph ps))
  have p0002 := @gRexbii (synWo ph ps) (.imp (.neg ph) ps) x A p0001
  have p0003 := (Nominal.biimpRefl (synWo (synWrex x A ph) (synWrex x A ps)))
  have p0004 := @gRalnex ph x A
  have p0005 :=
    @gImbi1i (synWral x A (.neg ph)) (.neg (synWrex x A ph)) (synWrex x A ps) p0004
  have p0006 :=
    @gBitr4i (synWo (synWrex x A ph) (synWrex x A ps))
      (.imp (.neg (synWrex x A ph)) (synWrex x A ps))
      (.imp (synWral x A (.neg ph)) (synWrex x A ps)) p0003 p0005
  have p0007 :=
    @gN3bitr4i (synWrex x A (.imp (.neg ph) ps))
      (.imp (synWral x A (.neg ph)) (synWrex x A ps)) (synWrex x A (synWo ph ps))
      (synWo (synWrex x A ph) (synWrex x A ps)) p0000 p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ralcomf`. -/
@[expose]
noncomputable def gRalcomf (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (hyp_ralcomf_1 : Nominal.NPrf (synWnfc y A))
    (hyp_ralcomf_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B ph)) (synWral y B (synWral x A ph))) :=
  by
  have p0000 := @gAncomsimp (.classMem (.cv x) A) (.classMem (.cv y) B) ph
  have p0001 :=
    @gN2albii (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)
      (.imp (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph) x y p0000
  have p0002 :=
    @gAlcom (.imp (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph) x y
  have p0003 :=
    @gBitri
      (.all x (.all y (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      (.all x (.all y (.imp (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      (.all y (.all x (.imp (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      p0001 p0002
  have p0004 :=
    @gR2alf ph x y A B
      (by
        aesop)
      hyp_ralcomf_1
  have p0005 :=
    @gR2alf ph y x B A
      (by
        aesop)
      hyp_ralcomf_2
  have p0006 :=
    @gN3bitr4i
      (.all x (.all y (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      (.all y (.all x (.imp (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      (synWral x A (synWral y B ph)) (synWral y B (synWral x A ph)) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_rexcomf`. -/
@[expose]
noncomputable def gRexcomf (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (hyp_ralcomf_1 : Nominal.NPrf (synWnfc y A))
    (hyp_ralcomf_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf
      (synWb (synWrex x A (synWrex y B ph)) (synWrex y B (synWrex x A ph))) :=
  by
  have p0000 := @gAncom (.classMem (.cv x) A) (.classMem (.cv y) B)
  have p0001 :=
    @gAnbi1i (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph p0000
  have p0002 :=
    @gN2exbii (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)
      (synWa (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph) x y p0001
  have p0003 :=
    @gExcom (synWa (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph) x y
  have p0004 :=
    @gBitri
      (synWex x (synWex y (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      (synWex x (synWex y (synWa (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      (synWex y (synWex x (synWa (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      p0002 p0003
  have p0005 :=
    @gR2exf ph x y A B
      (by
        aesop)
      hyp_ralcomf_1
  have p0006 :=
    @gR2exf ph y x B A
      (by
        aesop)
      hyp_ralcomf_2
  have p0007 :=
    @gN3bitr4i
      (synWex x (synWex y (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) ph)))
      (synWex y (synWex x (synWa (synWa (.classMem (.cv y) B) (.classMem (.cv x) A)) ph)))
      (synWrex x A (synWrex y B ph)) (synWrex y B (synWrex x A ph)) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ralcom`. -/
@[expose]
noncomputable def gRalcom (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B ph)) (synWral y B (synWral x A ph))) :=
  by
  have p0000 :=
    @gNfcv y A
      (by
        aesop)
  have p0001 :=
    @gNfcv x B
      (by
        aesop)
  have p0002 :=
    @gRalcomf ph x y A B
      (by
        aesop)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexcom`. -/
@[expose]
noncomputable def gRexcom (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWrex x A (synWrex y B ph)) (synWrex y B (synWrex x A ph))) :=
  by
  have p0000 :=
    @gNfcv y A
      (by
        aesop)
  have p0001 :=
    @gNfcv x B
      (by
        aesop)
  have p0002 :=
    @gRexcomf ph x y A B
      (by
        aesop)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_reean`. -/
@[expose]
noncomputable def gReean (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_reean_1 : Nominal.NPrf (synWnf y ph))
    (hyp_reean_2 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf
      (synWb (synWrex x A (synWrex y B (synWa ph ps)))
        (synWa (synWrex x A ph) (synWrex y B ps))) :=
  by
  have p0000 := @gAn4 (.classMem (.cv x) A) (.classMem (.cv y) B) ph ps
  have p0001 :=
    @gN2exbii
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (synWa ph ps))
      (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) B) ps)) x y
      p0000
  have p0002 :=
    @gNfv (.classMem (.cv x) A) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 := @gNfan (.classMem (.cv x) A) ph y p0002 hyp_reean_1
  have p0004 :=
    @gNfv (.classMem (.cv y) B) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @gNfan (.classMem (.cv y) B) ps x p0004 hyp_reean_2
  have p0006 :=
    @gEean (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) B) ps) x y p0003
      p0005
  have p0007 :=
    @gBitri
      (synWex x (synWex y
          (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (synWa ph ps))))
      (synWex x (synWex y
          (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) B) ps))))
      (synWa (synWex x (synWa (.classMem (.cv x) A) ph))
        (synWex y (synWa (.classMem (.cv y) B) ps)))
      p0001 p0006
  have p0008 :=
    @gR2ex (synWa ph ps) x y A B
      (by
        aesop)
      (by
        aesop)
  have p0009 := (Nominal.biimpRefl (synWrex x A ph))
  have p0010 := (Nominal.biimpRefl (synWrex y B ps))
  have p0011 :=
    @gAnbi12i (synWrex x A ph) (synWex x (synWa (.classMem (.cv x) A) ph))
      (synWrex y B ps) (synWex y (synWa (.classMem (.cv y) B) ps)) p0009 p0010
  have p0012 :=
    @gN3bitr4i
      (synWex x (synWex y
          (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (synWa ph ps))))
      (synWa (synWex x (synWa (.classMem (.cv x) A) ph))
        (synWex y (synWa (.classMem (.cv y) B) ps)))
      (synWrex x A (synWrex y B (synWa ph ps)))
      (synWa (synWrex x A ph) (synWrex y B ps)) p0007 p0008 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_reeanv`. -/
@[expose]
noncomputable def gReeanv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWrex x A (synWrex y B (synWa ph ps)))
        (synWa (synWrex x A ph) (synWrex y B ps))) :=
  by
  have p0000 :=
    @gNfv ph y
      (by
        aesop)
  have p0001 :=
    @gNfv ps x
      (by
        aesop)
  have p0002 :=
    @gReean ph ps x y A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rabid2`. -/
@[expose]
noncomputable def gRabid2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (.classEq A (synCrab x A ph)) (synWral x A ph)) :=
  by
  have p0000 :=
    @gEqabb (synWa (.classMem (.cv x) A) ph) x A
      (by
        aesop)
  have p0001 := @gPm471 (.classMem (.cv x) A) ph
  have p0002 :=
    @gAlbii (.imp (.classMem (.cv x) A) ph)
      (synWb (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) ph)) x p0001
  have p0003 :=
    @gBitr4i (.classEq A (.cab x (synWa (.classMem (.cv x) A) ph)))
      (.all x (synWb (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) ph)))
      (.all x (.imp (.classMem (.cv x) A) ph)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (synCrab x A ph))
  have p0005 :=
    @gEqeq2i (synCrab x A ph) (.cab x (synWa (.classMem (.cv x) A) ph)) A p0004
  have p0006 := (Nominal.biimpRefl (synWral x A ph))
  have p0007 :=
    @gN3bitr4i (.classEq A (.cab x (synWa (.classMem (.cv x) A) ph)))
      (.all x (.imp (.classMem (.cv x) A) ph)) (.classEq A (synCrab x A ph))
      (synWral x A ph) p0003 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_rabbi`. -/
@[expose]
noncomputable def gRabbi (ps : Wff) (ch : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWral x A (synWb ps ch)) (.classEq (synCrab x A ps) (synCrab x A ch))) :=
  by
  have p0000 :=
    @gAbbib (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv x) A) ch) x
  have p0001 := (Nominal.classEqRefl (synCrab x A ps))
  have p0002 := (Nominal.classEqRefl (synCrab x A ch))
  have p0003 :=
    @gEqeq12i (synCrab x A ps) (.cab x (synWa (.classMem (.cv x) A) ps))
      (synCrab x A ch) (.cab x (synWa (.classMem (.cv x) A) ch)) p0001 p0002
  have p0004 := (Nominal.biimpRefl (synWral x A (synWb ps ch)))
  have p0005 := @gPm532 (.classMem (.cv x) A) ps ch
  have p0006 :=
    @gAlbii (.imp (.classMem (.cv x) A) (synWb ps ch))
      (synWb (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv x) A) ch)) x p0005
  have p0007 :=
    @gBitri (synWral x A (synWb ps ch))
      (.all x (.imp (.classMem (.cv x) A) (synWb ps ch)))
      (.all x (synWb (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv x) A) ch)))
      p0004 p0006
  have p0008 :=
    @gN3bitr4ri
      (.classEq (.cab x (synWa (.classMem (.cv x) A) ps))
        (.cab x (synWa (.classMem (.cv x) A) ch)))
      (.all x (synWb (synWa (.classMem (.cv x) A) ps) (synWa (.classMem (.cv x) A) ch)))
      (.classEq (synCrab x A ps) (synCrab x A ch)) (synWral x A (synWb ps ch)) p0000
      p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_raleqf`. -/
@[expose]
noncomputable def gRaleqf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_raleq1f_1 : Nominal.NPrf (synWnfc x A))
    (hyp_raleq1f_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWral x A ph) (synWral x B ph))) :=
  by
  have p0000 := @gNfeq x A B hyp_raleq1f_1 hyp_raleq1f_2
  have p0001 := @gEleq2 A B (.cv x)
  have p0002 :=
    @gImbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B) ph p0001
  have p0003 :=
    @gAlbid (.classEq A B) (.imp (.classMem (.cv x) A) ph)
      (.imp (.classMem (.cv x) B) ph) x p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWral x A ph))
  have p0005 := (Nominal.biimpRefl (synWral x B ph))
  have p0006 :=
    @gN3bitr4g (.classEq A B) (.all x (.imp (.classMem (.cv x) A) ph))
      (.all x (.imp (.classMem (.cv x) B) ph)) (synWral x A ph) (synWral x B ph) p0003
      p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_rexeqf`. -/
@[expose]
noncomputable def gRexeqf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_raleq1f_1 : Nominal.NPrf (synWnfc x A))
    (hyp_raleq1f_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWrex x A ph) (synWrex x B ph))) :=
  by
  have p0000 := @gNfeq x A B hyp_raleq1f_1 hyp_raleq1f_2
  have p0001 := @gEleq2 A B (.cv x)
  have p0002 :=
    @gAnbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B) ph p0001
  have p0003 :=
    @gExbid (.classEq A B) (synWa (.classMem (.cv x) A) ph)
      (synWa (.classMem (.cv x) B) ph) x p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWrex x A ph))
  have p0005 := (Nominal.biimpRefl (synWrex x B ph))
  have p0006 :=
    @gN3bitr4g (.classEq A B) (synWex x (synWa (.classMem (.cv x) A) ph))
      (synWex x (synWa (.classMem (.cv x) B) ph)) (synWrex x A ph) (synWrex x B ph)
      p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_raleq`. -/
@[expose]
noncomputable def gRaleq (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWral x A ph) (synWral x B ph))) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfcv x B
      (by
        aesop)
  have p0002 := @gRaleqf ph x A B p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexeq`. -/
@[expose]
noncomputable def gRexeq (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWrex x A ph) (synWrex x B ph))) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfcv x B
      (by
        aesop)
  have p0002 := @gRexeqf ph x A B p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_raleqi`. -/
@[expose]
noncomputable def gRaleqi (ph : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWral x A ph) (synWral x B ph)) :=
  by
  have p0000 :=
    @gRaleq ph x A B
      (by
        aesop)
      (by
        aesop)
  have p0001 := Nominal.mp hyp_raleq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexeqi`. -/
@[expose]
noncomputable def gRexeqi (ph : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWrex x A ph) (synWrex x B ph)) :=
  by
  have p0000 :=
    @gRexeq ph x A B
      (by
        aesop)
      (by
        aesop)
  have p0001 := Nominal.mp hyp_raleq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_raleqdv`. -/
@[expose]
noncomputable def gRaleqdv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWral x A ps) (synWral x B ps))) :=
  by
  have p0000 :=
    @gRaleq ps x A B
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWral x A ps) (synWral x B ps)) hyp_raleq1d_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexeqdv`. -/
@[expose]
noncomputable def gRexeqdv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWrex x A ps) (synWrex x B ps))) :=
  by
  have p0000 :=
    @gRexeq ps x A B
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWrex x A ps) (synWrex x B ps)) hyp_raleq1d_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_raleqbi1dv`. -/
@[expose]
noncomputable def gRaleqbi1dv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleqd_1 : Nominal.NPrf (.imp (.classEq A B) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWral x A ph) (synWral x B ps))) :=
  by
  have p0000 :=
    @gRaleq ph x A B
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gRalbidv (.classEq A B) ph ps x B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_raleqd_1
  have p0002 :=
    @gBitrd (.classEq A B) (synWral x A ph) (synWral x B ph) (synWral x B ps) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexeqbi1dv`. -/
@[expose]
noncomputable def gRexeqbi1dv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_raleqd_1 : Nominal.NPrf (.imp (.classEq A B) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWrex x A ph) (synWrex x B ps))) :=
  by
  have p0000 :=
    @gRexeq ph x A B
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gRexbidv (.classEq A B) ph ps x B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_raleqd_1
  have p0002 :=
    @gBitrd (.classEq A B) (synWrex x A ph) (synWrex x B ph) (synWrex x B ps) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_raleqbidv`. -/
@[expose]
noncomputable def gRaleqbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_raleqbidv_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_raleqbidv_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWral x A ps) (synWral x B ch))) :=
  by
  have p0000 :=
    @gRaleqdv ph ps x A B
      (by
        aesop)
      (by
        aesop)
      hyp_raleqbidv_1
  have p0001 :=
    @gRalbidv ph ps ch x B
      (by
        aesop)
      hyp_raleqbidv_2
  have p0002 :=
    @gBitrd ph (synWral x A ps) (synWral x B ps) (synWral x B ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexeqbidv`. -/
@[expose]
noncomputable def gRexeqbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_raleqbidv_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_raleqbidv_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWrex x A ps) (synWrex x B ch))) :=
  by
  have p0000 :=
    @gRexeqdv ph ps x A B
      (by
        aesop)
      (by
        aesop)
      hyp_raleqbidv_1
  have p0001 :=
    @gRexbidv ph ps ch x B
      (by
        aesop)
      hyp_raleqbidv_2
  have p0002 :=
    @gBitrd ph (synWrex x A ps) (synWrex x B ps) (synWrex x B ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_reu5`. -/
@[expose]
noncomputable def gReu5 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWreu x A ph) (synWa (synWrex x A ph) (synWrmo x A ph))) :=
  by
  have p0000 := @gEu5 (synWa (.classMem (.cv x) A) ph) x
  have p0001 := (Nominal.biimpRefl (synWreu x A ph))
  have p0002 := (Nominal.biimpRefl (synWrex x A ph))
  have p0003 := (Nominal.biimpRefl (synWrmo x A ph))
  have p0004 :=
    @gAnbi12i (synWrex x A ph) (synWex x (synWa (.classMem (.cv x) A) ph))
      (synWrmo x A ph) (synWmo x (synWa (.classMem (.cv x) A) ph)) p0002 p0003
  have p0005 :=
    @gN3bitr4i (synWeu x (synWa (.classMem (.cv x) A) ph))
      (synWa (synWex x (synWa (.classMem (.cv x) A) ph))
        (synWmo x (synWa (.classMem (.cv x) A) ph)))
      (synWreu x A ph) (synWa (synWrex x A ph) (synWrmo x A ph)) p0000 p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cbvralf`. -/
@[expose]
noncomputable def gCbvralf (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_cbvralf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_cbvralf_2 : Nominal.NPrf (synWnfc y A))
    (hyp_cbvralf_3 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvralf_4 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvralf_5 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWral x A ph) (synWral y A ps)) :=
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
    @gNfv (.imp (.classMem (.cv x) A) ph) z
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 :=
    @gNfcri x z A
      (by
        aesop)
      hyp_cbvralf_1
  have p0002 :=
    @gNfs1v ph x z
      (by
        aesop)
  have p0003 := @gNfim (.classMem (.cv z) A) (synWsb z x ph) x p0001 p0002
  have p0004 := @gEleq1 (.cv x) (.cv z) A
  have p0005 := @gSbequ12 ph x z
  have p0006_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (synWb ph (synWsb z x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gImbi12d (.classEq (.cv x) (.cv z)) (.classMem (.cv x) A) (.classMem (.cv z) A) ph
      (synWsb z x ph) p0004 p0006_e01_recanon
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (synWb (.imp (.classMem (.cv x) A) ph)
          (.imp (.classMem (.cv z) A) (synWsb z x ph)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gCbval (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv z) A) (synWsb z x ph))
      x z p0000 p0003 p0007_e02_recanon
  have p0008 :=
    @gNfcri y z A
      (by
        aesop)
      hyp_cbvralf_2
  have p0009 :=
    @gNfsb ph x z y
      (by
        aesop)
      hyp_cbvralf_3
  have p0010 := @gNfim (.classMem (.cv z) A) (synWsb z x ph) y p0008 p0009
  have p0011 :=
    @gNfv (.imp (.classMem (.cv y) A) ps) z
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0012 := @gEleq1 (.cv z) (.cv y) A
  have p0013 := @gSbequ ph z y x
  have p0014 := @gSbie ph ps x y hyp_cbvralf_4 hyp_cbvralf_5
  have p0015_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y)) (synWb (synWsb z x ph) (synWsb y x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0015 :=
    @gSyl6bb (.classEq (.cv z) (.cv y)) (synWsb z x ph) (synWsb y x ph) ps
      p0015_e00_recanon p0014
  have p0016 :=
    @gImbi12d (.classEq (.cv z) (.cv y)) (.classMem (.cv z) A) (.classMem (.cv y) A)
      (synWsb z x ph) ps p0012 p0015
  have p0017_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (synWb (.imp (.classMem (.cv z) A) (synWsb z x ph))
          (.imp (.classMem (.cv y) A) ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gCbval (.imp (.classMem (.cv z) A) (synWsb z x ph)) (.imp (.classMem (.cv y) A) ps)
      z y p0010 p0011 p0017_e02_recanon
  have p0018 :=
    @gBitri (.all x (.imp (.classMem (.cv x) A) ph))
      (.all z (.imp (.classMem (.cv z) A) (synWsb z x ph)))
      (.all y (.imp (.classMem (.cv y) A) ps)) p0007 p0017
  have p0019 := (Nominal.biimpRefl (synWral x A ph))
  have p0020 := (Nominal.biimpRefl (synWral y A ps))
  have p0021 :=
    @gN3bitr4i (.all x (.imp (.classMem (.cv x) A) ph))
      (.all y (.imp (.classMem (.cv y) A) ps)) (synWral x A ph) (synWral y A ps) p0018
      p0019 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_cbvrexf`. -/
@[expose]
noncomputable def gCbvrexf (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_cbvralf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_cbvralf_2 : Nominal.NPrf (synWnfc y A))
    (hyp_cbvralf_3 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvralf_4 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvralf_5 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWrex x A ph) (synWrex y A ps)) :=
  by
  have p0000 := @gNfn ph y hyp_cbvralf_3
  have p0001 := @gNfn ps x hyp_cbvralf_4
  have p0002_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (synWb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_cbvralf_5
  have p0002 := @gNotbid (.classEq (.cv x) (.cv y)) ph ps p0002_e00_recanon
  have p0003_e04_recanon :
    Nominal.NPrf (.imp (.objEq x y) (synWb (.neg ph) (.neg ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @gCbvralf (.neg ph) (.neg ps) x y A hyp_cbvralf_1 hyp_cbvralf_2 p0000 p0001
      p0003_e04_recanon
  have p0004 := @gNotbii (synWral x A (.neg ph)) (synWral y A (.neg ps)) p0003
  have p0005 := @gDfrex2 ph x A
  have p0006 := @gDfrex2 ps y A
  have p0007 :=
    @gN3bitr4i (.neg (synWral x A (.neg ph))) (.neg (synWral y A (.neg ps)))
      (synWrex x A ph) (synWrex y A ps) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_cbvral`. -/
@[expose]
noncomputable def gCbvral (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbvral_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvral_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvral_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWral x A ph) (synWral y A ps)) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfcv y A
      (by
        aesop)
  have p0002 := @gCbvralf ph ps x y A p0000 p0001 hyp_cbvral_1 hyp_cbvral_2 hyp_cbvral_3
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbvrex`. -/
@[expose]
noncomputable def gCbvrex (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbvral_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvral_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvral_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWrex x A ph) (synWrex y A ps)) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfcv y A
      (by
        aesop)
  have p0002 := @gCbvrexf ph ps x y A p0000 p0001 hyp_cbvral_1 hyp_cbvral_2 hyp_cbvral_3
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbvralv`. -/
@[expose]
noncomputable def gCbvralv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_cbvralv_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWral x A ph) (synWral y A ps)) :=
  by
  have p0000 :=
    @gNfv ph y
      (by
        aesop)
  have p0001 :=
    @gNfv ps x
      (by
        aesop)
  have p0002 :=
    @gCbvral ph ps x y A
      (by
        aesop)
      (by
        aesop)
      p0000 p0001 hyp_cbvralv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbvrexv`. -/
@[expose]
noncomputable def gCbvrexv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_cbvralv_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWrex x A ph) (synWrex y A ps)) :=
  by
  have p0000 :=
    @gNfv ph y
      (by
        aesop)
  have p0001 :=
    @gNfv ps x
      (by
        aesop)
  have p0002 :=
    @gCbvrex ph ps x y A
      (by
        aesop)
      (by
        aesop)
      p0000 p0001 hyp_cbvralv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbvral2v`. -/
@[expose]
noncomputable def gCbvral2v (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (w : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_w : w ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv)
    (dv_ch_w : w ∉ ch.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_z : z ∉ ph.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y) (dv_y_z : y ≠ z)
    (hyp_cbvral2v_1 : Nominal.NPrf (.imp (.objEq x z) (synWb ph ch)))
    (hyp_cbvral2v_2 : Nominal.NPrf (.imp (.objEq y w) (synWb ch ps))) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B ph)) (synWral z A (synWral w B ps))) :=
  by
  have p0000_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (synWb ph ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_cbvral2v_1
  have p0000 :=
    @gRalbidv (.classEq (.cv x) (.cv z)) ph ch y B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0000_e00_recanon
  have p0001_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (synWb (synWral y B ph) (synWral y B ch))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWral
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0001 :=
    @gCbvralv (synWral y B ph) (synWral y B ch) x z A
      (by
        aesop)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      p0001_e00_recanon
  have p0002 :=
    @gCbvralv ch ps y w B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      hyp_cbvral2v_2
  have p0003 := @gRalbii (synWral y B ch) (synWral w B ps) z A p0002
  have p0004 :=
    @gBitri (synWral x A (synWral y B ph)) (synWral z A (synWral y B ch))
      (synWral z A (synWral w B ps)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cbvrexsv`. -/
@[expose]
noncomputable def gCbvrexsv (ph : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf (synWb (synWrex x A ph) (synWrex y A (synWsb y x ph))) :=
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
    @gNfv ph z
      (by
        aesop)
  have p0001 :=
    @gNfs1v ph x z
      (by
        aesop)
  have p0002 := @gSbequ12 ph x z
  have p0003 :=
    @gCbvrex ph (synWsb z x ph) x z A
      (by
        aesop)
      (by
        aesop)
      p0000 p0001 p0002
  have p0004 :=
    @gNfv ph y
      (by
        aesop)
  have p0005 :=
    @gNfsb ph x z y
      (by
        aesop)
      p0004
  have p0006 :=
    @gNfv (synWsb y x ph) z
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb,
              Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
  have p0007 := @gSbequ ph z y x
  have p0008 :=
    @gCbvrex (synWsb z x ph) (synWsb y x ph) z y A
      (by
        aesop)
      (by
        aesop)
      p0005 p0006 p0007
  have p0009 :=
    @gBitri (synWrex x A ph) (synWrex z A (synWsb z x ph))
      (synWrex y A (synWsb y x ph)) p0003 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_rabbidva`. -/
@[expose]
noncomputable def gRabbidva (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_rabbidva_1 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (synCrab x A ps) (synCrab x A ch))) :=
  by
  have p0000 :=
    @gRalrimiva ph (synWb ps ch) x A
      (by
        aesop)
      hyp_rabbidva_1
  have p0001 := @gRabbi ps ch x A
  have p0002 :=
    @gSylib ph (synWral x A (synWb ps ch))
      (.classEq (synCrab x A ps) (synCrab x A ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rabbidv`. -/
@[expose]
noncomputable def gRabbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_rabbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (synCrab x A ps) (synCrab x A ch))) :=
  by
  have p0000 := @gAdantr ph (synWb ps ch) (.classMem (.cv x) A) hyp_rabbidv_1
  have p0001 :=
    @gRabbidva ph ps ch x A
      (by
        aesop)
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rabeqf`. -/
@[expose]
noncomputable def gRabeqf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_rabeqf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_rabeqf_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCrab x A ph) (synCrab x B ph))) :=
  by
  have p0000 := @gNfeq x A B hyp_rabeqf_1 hyp_rabeqf_2
  have p0001 := @gEleq2 A B (.cv x)
  have p0002 :=
    @gAnbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B) ph p0001
  have p0003 :=
    @gAbbid (.classEq A B) (synWa (.classMem (.cv x) A) ph)
      (synWa (.classMem (.cv x) B) ph) x p0000 p0002
  have p0004 := (Nominal.classEqRefl (synCrab x A ph))
  have p0005 := (Nominal.classEqRefl (synCrab x B ph))
  have p0006 :=
    @gN3eqtr4g (.classEq A B) (.cab x (synWa (.classMem (.cv x) A) ph))
      (.cab x (synWa (.classMem (.cv x) B) ph)) (synCrab x A ph) (synCrab x B ph) p0003
      p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_rabeq`. -/
@[expose]
noncomputable def gRabeq (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCrab x A ph) (synCrab x B ph))) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfcv x B
      (by
        aesop)
  have p0002 := @gRabeqf ph x A B p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_vex`. -/
@[expose]
noncomputable def gVex (x : Var) : Nominal.NPrf (.classMem (.cv x) (synCvv)) :=
  by
  have p0000 := @gEqid (.cv x)
  have p0001 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfV x
  have p0002_e00_recanon :
    Nominal.NPrf (.classEq (synCvv) (.cab x (.classEq (.cv x) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0001
  have p0002 := @gEqabri (.classEq (.cv x) (.cv x)) x (synCvv) p0002_e00_recanon
  have p0003 :=
    @gMpbir (.classMem (.cv x) (synCvv)) (.classEq (.cv x) (.cv x)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_isset`. -/
@[expose]
noncomputable def gIsset (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (.classMem A (synCvv)) (synWex x (.classEq (.cv x) A))) :=
  by
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A
      (synCvv) (by
        aesop) (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop)))
  have p0001 := @gVex x
  have p0002 := @gBiantru (.classMem (.cv x) (synCvv)) (.classEq (.cv x) A) p0001
  have p0003 :=
    @gExbii (.classEq (.cv x) A)
      (synWa (.classEq (.cv x) A) (.classMem (.cv x) (synCvv))) x p0002
  have p0004 :=
    @gBitr4i (.classMem A (synCvv))
      (synWex x (synWa (.classEq (.cv x) A) (.classMem (.cv x) (synCvv))))
      (synWex x (.classEq (.cv x) A)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_issetf`. -/
@[expose]
noncomputable def gIssetf (x : Var) (A : Class)
    (hyp_issetf_1 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf (synWb (.classMem A (synCvv)) (synWex x (.classEq (.cv x) A))) :=
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
    @gIsset y A
      (by
        aesop)
  have p0001 :=
    @gNfeq2 x (.cv y) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      hyp_issetf_1
  have p0002 :=
    @gNfv (.classEq (.cv x) A) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 := @gEqeq1 (.cv y) (.cv x) A
  have p0004_e02_recanon :
    Nominal.NPrf (.imp (.objEq y x) (synWb (.classEq (.cv y) A) (.classEq (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @gCbvex (.classEq (.cv y) A) (.classEq (.cv x) A) y x p0001 p0002 p0004_e02_recanon
  have p0005 :=
    @gBitri (.classMem A (synCvv)) (synWex y (.classEq (.cv y) A))
      (synWex x (.classEq (.cv x) A)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_isseti`. -/
@[expose]
noncomputable def gIsseti (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_isseti_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWex x (.classEq (.cv x) A)) :=
  by
  have p0000 :=
    @gIsset x A
      (by
        aesop)
  have p0001 :=
    @gMpbi (.classMem A (synCvv)) (synWex x (.classEq (.cv x) A)) hyp_isseti_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elex`. -/
@[expose]
noncomputable def gElex (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem A (synCvv))) :=
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
  have p0000 := @gExsimpl (.classEq (.cv x) A) (.classMem (.cv x) B) x
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A B (by
        aesop) (by
        aesop))
  have p0002 :=
    @gIsset x A
      (by
        aesop)
  have p0003 :=
    @gN3imtr4i (synWex x (synWa (.classEq (.cv x) A) (.classMem (.cv x) B)))
      (synWex x (.classEq (.cv x) A)) (.classMem A B) (.classMem A (synCvv)) p0000 p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elexi`. -/
@[expose]
noncomputable def gElexi (A : Class) (B : Class)
    (hyp_elisseti_1 : Nominal.NPrf (.classMem A B)) :
    Nominal.NPrf (.classMem A (synCvv)) :=
  by
  have p0000 := @gElex A B
  have p0001 := Nominal.mp hyp_elisseti_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elisset`. -/
@[expose]
noncomputable def gElisset (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem A V) (synWex x (.classEq (.cv x) A))) :=
  by
  have p0000 := @gElex A V
  have p0001 :=
    @gIsset x A
      (by
        aesop)
  have p0002 :=
    @gSylib (.classMem A V) (.classMem A (synCvv)) (synWex x (.classEq (.cv x) A))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ralv`. -/
@[expose]
noncomputable def gRalv (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWral x (synCvv) ph) (.all x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x (synCvv) ph))
  have p0001 := @gVex x
  have p0002 := @gA1bi (.classMem (.cv x) (synCvv)) ph p0001
  have p0003 := @gAlbii ph (.imp (.classMem (.cv x) (synCvv)) ph) x p0002
  have p0004 :=
    @gBitr4i (synWral x (synCvv) ph) (.all x (.imp (.classMem (.cv x) (synCvv)) ph))
      (.all x ph) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_rexv`. -/
@[expose]
noncomputable def gRexv (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWrex x (synCvv) ph) (synWex x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWrex x (synCvv) ph))
  have p0001 := @gVex x
  have p0002 := @gBiantrur (.classMem (.cv x) (synCvv)) ph p0001
  have p0003 := @gExbii ph (synWa (.classMem (.cv x) (synCvv)) ph) x p0002
  have p0004 :=
    @gBitr4i (synWrex x (synCvv) ph)
      (synWex x (synWa (.classMem (.cv x) (synCvv)) ph)) (synWex x ph) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_rabab`. -/
@[expose]
noncomputable def gRabab (ph : Wff) (x : Var) :
    Nominal.NPrf (.classEq (synCrab x (synCvv) ph) (.cab x ph)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCrab x (synCvv) ph))
  have p0001 := @gVex x
  have p0002 := @gBiantrur (.classMem (.cv x) (synCvv)) ph p0001
  have p0003 := @gAbbii ph (synWa (.classMem (.cv x) (synCvv)) ph) x p0002
  have p0004 :=
    @gEqtr4i (synCrab x (synCvv) ph) (.cab x (synWa (.classMem (.cv x) (synCvv)) ph))
      (.cab x ph) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ralcom4`. -/
@[expose]
noncomputable def gRalcom4 (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWb (synWral x A (.all y ph)) (.all y (synWral x A ph))) :=
  by
  have p0000 :=
    @gRalcom ph x y A (synCvv)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      (by
        aesop)
  have p0001 := @gRalv ph y
  have p0002 := @gRalbii (synWral y (synCvv) ph) (.all y ph) x A p0001
  have p0003 := @gRalv (synWral x A ph) y
  have p0004 :=
    @gN3bitr3i (synWral x A (synWral y (synCvv) ph))
      (synWral y (synCvv) (synWral x A ph)) (synWral x A (.all y ph))
      (.all y (synWral x A ph)) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_rexcom4`. -/
@[expose]
noncomputable def gRexcom4 (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWb (synWrex x A (synWex y ph)) (synWex y (synWrex x A ph))) :=
  by
  have p0000 :=
    @gRexcom ph x y A (synCvv)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      (by
        aesop)
  have p0001 := @gRexv ph y
  have p0002 := @gRexbii (synWrex y (synCvv) ph) (synWex y ph) x A p0001
  have p0003 := @gRexv (synWrex x A ph) y
  have p0004 :=
    @gN3bitr3i (synWrex x A (synWrex y (synCvv) ph))
      (synWrex y (synCvv) (synWrex x A ph)) (synWrex x A (synWex y ph))
      (synWex y (synWrex x A ph)) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ceqsalg`. -/
@[expose]
noncomputable def gCeqsalg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (hyp_ceqsalg_1 : Nominal.NPrf (synWnf x ps))
    (hyp_ceqsalg_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.all x (.imp (.classEq (.cv x) A) ph)) ps)) :=
  by
  have p0000 :=
    @gElisset x A V
      (by
        aesop)
  have p0001 := @gNfa1 (.imp (.classEq (.cv x) A) ph) x
  have p0002 := @gBiimpd (.classEq (.cv x) A) ph ps hyp_ceqsalg_2
  have p0003 := @gA2i (.classEq (.cv x) A) ph ps p0002
  have p0004 :=
    @gSps (.imp (.classEq (.cv x) A) ph) (.imp (.classEq (.cv x) A) ps) x p0003
  have p0005 :=
    @gExlimd (.all x (.imp (.classEq (.cv x) A) ph)) (.classEq (.cv x) A) ps x p0001
      hyp_ceqsalg_1 p0004
  have p0006 :=
    @gSyl5com (.classMem A V) (synWex x (.classEq (.cv x) A))
      (.all x (.imp (.classEq (.cv x) A) ph)) ps p0000 p0005
  have p0007 := @gBiimprcd (.classEq (.cv x) A) ph ps hyp_ceqsalg_2
  have p0008 := @gAlrimi ps (.imp (.classEq (.cv x) A) ph) x hyp_ceqsalg_1 p0007
  have p0009 :=
    @gImpbid1 (.classMem A V) (.all x (.imp (.classEq (.cv x) A) ph)) ps p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_ceqsal`. -/
@[expose]
noncomputable def gCeqsal (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_ceqsal_1 : Nominal.NPrf (synWnf x ps))
    (hyp_ceqsal_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ceqsal_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x (.imp (.classEq (.cv x) A) ph)) ps) :=
  by
  have p0000 :=
    @gCeqsalg ph ps x A (synCvv)
      (by
        aesop)
      hyp_ceqsal_1 hyp_ceqsal_3
  have p0001 := Nominal.mp hyp_ceqsal_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ceqsalv`. -/
@[expose]
noncomputable def gCeqsalv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsalv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ceqsalv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x (.imp (.classEq (.cv x) A) ph)) ps) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 :=
    @gCeqsal ph ps x A
      (by
        aesop)
      p0000 hyp_ceqsalv_1 hyp_ceqsalv_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ceqsex`. -/
@[expose]
noncomputable def gCeqsex (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_ceqsex_1 : Nominal.NPrf (synWnf x ps))
    (hyp_ceqsex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ceqsex_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWex x (synWa (.classEq (.cv x) A) ph)) ps) :=
  by
  have p0000 := @gBiimpa (.classEq (.cv x) A) ph ps hyp_ceqsex_3
  have p0001 := @gExlimi (synWa (.classEq (.cv x) A) ph) ps x hyp_ceqsex_1 p0000
  have p0002 := @gBiimprcd (.classEq (.cv x) A) ph ps hyp_ceqsex_3
  have p0003 := @gAlrimi ps (.imp (.classEq (.cv x) A) ph) x hyp_ceqsex_1 p0002
  have p0004 :=
    @gIsseti x A
      (by
        aesop)
      hyp_ceqsex_2
  have p0005 := @gExintr (.classEq (.cv x) A) ph x
  have p0006 :=
    @gEe10 ps (.all x (.imp (.classEq (.cv x) A) ph)) (synWex x (.classEq (.cv x) A))
      (synWex x (synWa (.classEq (.cv x) A) ph)) p0003 p0004 p0005
  have p0007 := @gImpbii (synWex x (synWa (.classEq (.cv x) A) ph)) ps p0001 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ceqsexv`. -/
@[expose]
noncomputable def gCeqsexv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsexv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ceqsexv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWex x (synWa (.classEq (.cv x) A) ph)) ps) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 :=
    @gCeqsex ph ps x A
      (by
        aesop)
      p0000 hyp_ceqsexv_1 hyp_ceqsexv_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ceqsex2`. -/
@[expose]
noncomputable def gCeqsex2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_ceqsex2_1 : Nominal.NPrf (synWnf x ps))
    (hyp_ceqsex2_2 : Nominal.NPrf (synWnf y ch))
    (hyp_ceqsex2_3 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ceqsex2_4 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_ceqsex2_5 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_ceqsex2_6 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch))) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph)))
        ch) :=
  by
  have p0000 := @gN3anass (.classEq (.cv x) A) (.classEq (.cv y) B) ph
  have p0001 :=
    @gExbii (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph)
      (synWa (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph)) y p0000
  have p0002 :=
    @gN1942v (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gBitri (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph))
      (synWex y (synWa (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph)))
      (synWa (.classEq (.cv x) A) (synWex y (synWa (.classEq (.cv y) B) ph))) p0001
      p0002
  have p0004 :=
    @gExbii (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph))
      (synWa (.classEq (.cv x) A) (synWex y (synWa (.classEq (.cv y) B) ph))) x p0003
  have p0005 :=
    @gNfv (.classEq (.cv y) B) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 := @gNfan (.classEq (.cv y) B) ps x p0005 hyp_ceqsex2_1
  have p0007 := @gNfex (synWa (.classEq (.cv y) B) ps) x y p0006
  have p0008 := @gAnbi2d (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) hyp_ceqsex2_5
  have p0009 :=
    @gExbidv (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph)
      (synWa (.classEq (.cv y) B) ps) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0008
  have p0010 :=
    @gCeqsex (synWex y (synWa (.classEq (.cv y) B) ph))
      (synWex y (synWa (.classEq (.cv y) B) ps)) x A
      (by
        aesop)
      p0007 hyp_ceqsex2_3 p0009
  have p0011 :=
    @gCeqsex ps ch y B
      (by
        aesop)
      hyp_ceqsex2_2 hyp_ceqsex2_4 hyp_ceqsex2_6
  have p0012 :=
    @gN3bitri
      (synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph)))
      (synWex x (synWa (.classEq (.cv x) A) (synWex y (synWa (.classEq (.cv y) B) ph))))
      (synWex y (synWa (.classEq (.cv y) B) ps)) ch p0004 p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_ceqsex2v`. -/
@[expose]
noncomputable def gCeqsex2v (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ch_y : y ∉ ch.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ceqsex2v_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ceqsex2v_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_ceqsex2v_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_ceqsex2v_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch))) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) ph)))
        ch) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 :=
    @gNfv ch y
      (by
        aesop)
  have p0002 :=
    @gCeqsex2 ph ps ch x y A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      p0000 p0001 hyp_ceqsex2v_1 hyp_ceqsex2v_2 hyp_ceqsex2v_3 hyp_ceqsex2v_4
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_vtoclgft`. -/
@[expose]
noncomputable def gVtoclgft (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWa (synWnfc x A) (synWnf x ps))
          (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
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
  have p0000 := @gElex A V
  have p0001 :=
    @gElisset z A (synCvv)
      (by
        aesop)
  have p0002 :=
    @gN3ad2ant3 (.classMem A (synCvv)) (synWa (synWnfc x A) (synWnf x ps))
      (synWex z (.classEq (.cv z) A))
      (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph)) p0001
  have p0003 := @gNfnfc1 x A
  have p0004 :=
    @gNfcvd (synWnfc x A) x (.cv z)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @gId (synWnfc x A)
  have p0006 := @gNfeqd (synWnfc x A) x (.cv z) A p0004 p0005
  have p0007 := @gEqeq1 (.cv z) (.cv x) A
  have p0008 :=
    @gA1i
      (.imp (.classEq (.cv z) (.cv x)) (synWb (.classEq (.cv z) A) (.classEq (.cv x) A)))
      (synWnfc x A) p0007
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (synWnfc x A)
        (.imp (.objEq z x) (synWb (.classEq (.cv z) A) (.classEq (.cv x) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWnfc synWnf synWb
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gCbvexd (synWnfc x A) (.classEq (.cv z) A) (.classEq (.cv x) A) z x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wnfc,
              Finset.mem_erase] at ⊢;
            aesop))
      p0003 p0006 p0009_e02_recanon
  have p0010 :=
    @gAd2antrr (synWnfc x A)
      (synWb (synWex z (.classEq (.cv z) A)) (synWex x (.classEq (.cv x) A)))
      (synWnf x ps)
      (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph)) p0009
  have p0011 :=
    @gN3adant3 (synWa (synWnfc x A) (synWnf x ps))
      (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
      (synWb (synWex z (.classEq (.cv z) A)) (synWex x (.classEq (.cv x) A)))
      (.classMem A (synCvv)) p0010
  have p0012 :=
    @gMpbid
      (synW3a (synWa (synWnfc x A) (synWnf x ps))
        (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
        (.classMem A (synCvv)))
      (synWex z (.classEq (.cv z) A)) (synWex x (.classEq (.cv x) A)) p0002 p0011
  have p0013 := @gBi1 ph ps
  have p0014 := @gImim2i (synWb ph ps) (.imp ph ps) (.classEq (.cv x) A) p0013
  have p0015 :=
    @gCom23 (.imp (.classEq (.cv x) A) (synWb ph ps)) (.classEq (.cv x) A) ph ps p0014
  have p0016 :=
    @gImp (.imp (.classEq (.cv x) A) (synWb ph ps)) ph (.imp (.classEq (.cv x) A) ps)
      p0015
  have p0017 :=
    @gAlanimi (.imp (.classEq (.cv x) A) (synWb ph ps)) ph
      (.imp (.classEq (.cv x) A) ps) x p0016
  have p0018 :=
    @gN3ad2ant2 (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
      (synWa (synWnfc x A) (synWnf x ps)) (.all x (.imp (.classEq (.cv x) A) ps))
      (.classMem A (synCvv)) p0017
  have p0019 :=
    @gSimp1r (synWnfc x A) (synWnf x ps)
      (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
      (.classMem A (synCvv))
  have p0020 := @gN1923t (.classEq (.cv x) A) ps x
  have p0021 :=
    @gSyl
      (synW3a (synWa (synWnfc x A) (synWnf x ps))
        (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
        (.classMem A (synCvv)))
      (synWnf x ps)
      (synWb (.all x (.imp (.classEq (.cv x) A) ps))
        (.imp (synWex x (.classEq (.cv x) A)) ps))
      p0019 p0020
  have p0022 :=
    @gMpbid
      (synW3a (synWa (synWnfc x A) (synWnf x ps))
        (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
        (.classMem A (synCvv)))
      (.all x (.imp (.classEq (.cv x) A) ps)) (.imp (synWex x (.classEq (.cv x) A)) ps)
      p0018 p0021
  have p0023 :=
    @gMpd
      (synW3a (synWa (synWnfc x A) (synWnf x ps))
        (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
        (.classMem A (synCvv)))
      (synWex x (.classEq (.cv x) A)) ps p0012 p0022
  have p0024 :=
    @gSyl3an3 (.classMem A V) (synWa (synWnfc x A) (synWnf x ps))
      (synWa (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (.all x ph))
      (.classMem A (synCvv)) ps p0000 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_vtocldf`. -/
@[expose]
noncomputable def gVtocldf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (V : Class) (hyp_vtocld_1 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_vtocld_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (synWb ps ch)))
    (hyp_vtocld_3 : Nominal.NPrf (.imp ph ps))
    (hyp_vtocldf_4 : Nominal.NPrf (synWnf x ph))
    (hyp_vtocldf_5 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_vtocldf_6 : Nominal.NPrf (.imp ph (synWnf x ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gEx ph (.classEq (.cv x) A) (synWb ps ch) hyp_vtocld_2
  have p0001 :=
    @gAlrimi ph (.imp (.classEq (.cv x) A) (synWb ps ch)) x hyp_vtocldf_4 p0000
  have p0002 := @gAlrimi ph ps x hyp_vtocldf_4 hyp_vtocld_3
  have p0003 := @gVtoclgft ps ch x A V
  have p0004 :=
    @gSyl221anc ph (synWnfc x A) (synWnf x ch)
      (.all x (.imp (.classEq (.cv x) A) (synWb ps ch))) (.all x ps) (.classMem A V) ch
      hyp_vtocldf_5 hyp_vtocldf_6 p0001 p0002 hyp_vtocld_1 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_vtocld`. -/
@[expose]
noncomputable def gVtocld (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (V : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_vtocld_1 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_vtocld_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (synWb ps ch)))
    (hyp_vtocld_3 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 :=
    @gNfcvd ph x A
      (by
        aesop)
  have p0002 :=
    @gNfvd ph ch x
      (by
        aesop)
  have p0003 :=
    @gVtocldf ph ps ch x A V hyp_vtocld_1 hyp_vtocld_2 hyp_vtocld_3 p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_vtoclf`. -/
@[expose]
noncomputable def gVtoclf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_vtoclf_1 : Nominal.NPrf (synWnf x ps))
    (hyp_vtoclf_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_vtoclf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtoclf_4 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  have p0000 :=
    @gIsseti x A
      (by
        aesop)
      hyp_vtoclf_2
  have p0001 := @gBiimpd (.classEq (.cv x) A) ph ps hyp_vtoclf_3
  have p0002 := @gEximi (.classEq (.cv x) A) (.imp ph ps) x p0001
  have p0003 := Nominal.mp p0000 p0002
  have p0004 := @gN1936i ph ps x hyp_vtoclf_1 p0003
  have p0005 := @gMpg ph ps x p0004 hyp_vtoclf_4
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_vtocl`. -/
@[expose]
noncomputable def gVtocl (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_vtocl_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_vtocl_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtocl_3 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 :=
    @gVtoclf ph ps x A
      (by
        aesop)
      p0000 hyp_vtocl_1 hyp_vtocl_2 hyp_vtocl_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_vtocl2`. -/
@[expose]
noncomputable def gVtocl2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_vtocl2_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_vtocl2_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_vtocl2_3 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps)))
    (hyp_vtocl2_4 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  have p0000 :=
    @gIsseti x A
      (by
        aesop)
      hyp_vtocl2_1
  have p0001 :=
    @gIsseti y B
      (by
        aesop)
      hyp_vtocl2_2
  have p0002 :=
    @gEeanv (.classEq (.cv x) A) (.classEq (.cv y) B) x y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gBiimpd (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph ps hyp_vtocl2_3
  have p0004 :=
    @gN2eximi (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.imp ph ps) x y p0003
  have p0005 :=
    @gSylbir (synWa (synWex x (.classEq (.cv x) A)) (synWex y (.classEq (.cv y) B)))
      (synWex x (synWex y (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))))
      (synWex x (synWex y (.imp ph ps))) p0002 p0004
  have p0006 :=
    @gMp2an (synWex x (.classEq (.cv x) A)) (synWex y (.classEq (.cv y) B))
      (synWex x (synWex y (.imp ph ps))) p0000 p0001 p0005
  have p0007 :=
    @gN1936v ph ps y
      (by
        aesop)
  have p0008 := @gExbii (synWex y (.imp ph ps)) (.imp (.all y ph) ps) x p0007
  have p0009 :=
    @gMpbi (synWex x (synWex y (.imp ph ps))) (synWex x (.imp (.all y ph) ps)) p0006
      p0008
  have p0010 :=
    @gN1936aiv (.all y ph) ps x
      (by
        aesop)
      p0009
  have p0011 := Nominal.gen hyp_vtocl2_4 y
  have p0012 := @gMpg (.all y ph) ps x p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_vtoclb`. -/
@[expose]
noncomputable def gVtoclb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var)
    (A : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_th_x : x ∉ th.fv)
    (hyp_vtoclb_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_vtoclb_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ch)))
    (hyp_vtoclb_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ps th)))
    (hyp_vtoclb_4 : Nominal.NPrf (synWb ph ps)) : Nominal.NPrf (synWb ch th) :=
  by
  have p0000 := @gBibi12d (.classEq (.cv x) A) ph ch ps th hyp_vtoclb_2 hyp_vtoclb_3
  have p0001 :=
    @gVtocl (synWb ph ps) (synWb ch th) x A
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_vtoclb_1 p0000 hyp_vtoclb_4
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_vtoclgf`. -/
@[expose]
noncomputable def gVtoclgf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (hyp_vtoclgf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_vtoclgf_2 : Nominal.NPrf (synWnf x ps))
    (hyp_vtoclgf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtoclgf_4 : Nominal.NPrf ph) : Nominal.NPrf (.imp (.classMem A V) ps) :=
  by
  have p0000 := @gElex A V
  have p0001 := @gIssetf x A hyp_vtoclgf_1
  have p0002 := @gMpbii (.classEq (.cv x) A) ph ps hyp_vtoclgf_4 hyp_vtoclgf_3
  have p0003 := @gExlimi (.classEq (.cv x) A) ps x hyp_vtoclgf_2 p0002
  have p0004 :=
    @gSylbi (.classMem A (synCvv)) (synWex x (.classEq (.cv x) A)) ps p0001 p0003
  have p0005 := @gSyl (.classMem A V) (.classMem A (synCvv)) ps p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_vtoclg`. -/
@[expose]
noncomputable def gVtoclg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_vtoclg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtoclg_2 : Nominal.NPrf ph) : Nominal.NPrf (.imp (.classMem A V) ps) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfv ps x
      (by
        aesop)
  have p0002 := @gVtoclgf ph ps x A V p0000 p0001 hyp_vtoclg_1 hyp_vtoclg_2
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_vtoclbg`. -/
@[expose]
noncomputable def gVtoclbg (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var)
    (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_th_x : x ∉ th.fv)
    (hyp_vtoclbg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ch)))
    (hyp_vtoclbg_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ps th)))
    (hyp_vtoclbg_3 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (.imp (.classMem A V) (synWb ch th)) :=
  by
  have p0000 := @gBibi12d (.classEq (.cv x) A) ph ch ps th hyp_vtoclbg_1 hyp_vtoclbg_2
  have p0001 :=
    @gVtoclg (synWb ph ps) (synWb ch th) x A V
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 hyp_vtoclbg_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_vtocl2gf`. -/
@[expose]
noncomputable def gVtocl2gf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (V : Class) (W : Class)
    (hyp_vtocl2gf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_vtocl2gf_2 : Nominal.NPrf (synWnfc y A))
    (hyp_vtocl2gf_3 : Nominal.NPrf (synWnfc y B))
    (hyp_vtocl2gf_4 : Nominal.NPrf (synWnf x ps))
    (hyp_vtocl2gf_5 : Nominal.NPrf (synWnf y ch))
    (hyp_vtocl2gf_6 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtocl2gf_7 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch)))
    (hyp_vtocl2gf_8 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp (synWa (.classMem A V) (.classMem B W)) ch) :=
  by
  have p0000 := @gElex A V
  have p0001 :=
    @gNfel1 y A (synCvv)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      hyp_vtocl2gf_2
  have p0002 := @gNfim (.classMem A (synCvv)) ch y p0001 hyp_vtocl2gf_5
  have p0003 :=
    @gImbi2d (.classEq (.cv y) B) ps ch (.classMem A (synCvv)) hyp_vtocl2gf_7
  have p0004 :=
    @gVtoclgf ph ps x A (synCvv) hyp_vtocl2gf_1 hyp_vtocl2gf_4 hyp_vtocl2gf_6
      hyp_vtocl2gf_8
  have p0005 :=
    @gVtoclgf (.imp (.classMem A (synCvv)) ps) (.imp (.classMem A (synCvv)) ch) y B W
      hyp_vtocl2gf_3 p0002 p0003 p0004
  have p0006 :=
    @gMpan9 (.classMem A V) (.classMem A (synCvv)) (.classMem B W) ch p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_vtocl2g`. -/
@[expose]
noncomputable def gVtocl2g (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_ch_y : y ∉ ch.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_vtocl2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtocl2g_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch)))
    (hyp_vtocl2g_3 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp (synWa (.classMem A V) (.classMem B W)) ch) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfcv y A
      (by
        aesop)
  have p0002 :=
    @gNfcv y B
      (by
        aesop)
  have p0003 :=
    @gNfv ps x
      (by
        aesop)
  have p0004 :=
    @gNfv ch y
      (by
        aesop)
  have p0005 :=
    @gVtocl2gf ph ps ch x y A B V W p0000 p0001 p0002 p0003 p0004 hyp_vtocl2g_1
      hyp_vtocl2g_2 hyp_vtocl2g_3
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_vtoclgaf`. -/
@[expose]
noncomputable def gVtoclgaf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) (hyp_vtoclgaf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_vtoclgaf_2 : Nominal.NPrf (synWnf x ps))
    (hyp_vtoclgaf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtoclgaf_4 : Nominal.NPrf (.imp (.classMem (.cv x) B) ph)) :
    Nominal.NPrf (.imp (.classMem A B) ps) :=
  by
  have p0000 :=
    @gNfel1 x A B
      (by
        aesop)
      hyp_vtoclgaf_1
  have p0001 := @gNfim (.classMem A B) ps x p0000 hyp_vtoclgaf_2
  have p0002 := @gEleq1 (.cv x) A B
  have p0003 :=
    @gImbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0002
      hyp_vtoclgaf_3
  have p0004 :=
    @gVtoclgf (.imp (.classMem (.cv x) B) ph) (.imp (.classMem A B) ps) x A B
      hyp_vtoclgaf_1 p0001 p0003 hyp_vtoclgaf_4
  have p0005 := @gPm243i (.classMem A B) ps p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_vtoclga`. -/
@[expose]
noncomputable def gVtoclga (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_vtoclga_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtoclga_2 : Nominal.NPrf (.imp (.classMem (.cv x) B) ph)) :
    Nominal.NPrf (.imp (.classMem A B) ps) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfv ps x
      (by
        aesop)
  have p0002 :=
    @gVtoclgaf ph ps x A B
      (by
        aesop)
      p0000 p0001 hyp_vtoclga_1 hyp_vtoclga_2
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_vtocl2gaf`. -/
@[expose]
noncomputable def gVtocl2gaf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y)
    (hyp_vtocl2gaf_a : Nominal.NPrf (synWnfc x A))
    (hyp_vtocl2gaf_b : Nominal.NPrf (synWnfc y A))
    (hyp_vtocl2gaf_c : Nominal.NPrf (synWnfc y B))
    (hyp_vtocl2gaf_1 : Nominal.NPrf (synWnf x ps))
    (hyp_vtocl2gaf_2 : Nominal.NPrf (synWnf y ch))
    (hyp_vtocl2gaf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtocl2gaf_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch)))
    (hyp_vtocl2gaf_5 :
      Nominal.NPrf (.imp (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)) ph)) :
    Nominal.NPrf (.imp (synWa (.classMem A C) (.classMem B D)) ch) :=
  by
  have p0000 :=
    @gNfel1 x A C
      (by
        aesop)
      hyp_vtocl2gaf_a
  have p0001 :=
    @gNfv (.classMem (.cv y) D) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @gNfan (.classMem A C) (.classMem (.cv y) D) x p0000 p0001
  have p0003 :=
    @gNfim (synWa (.classMem A C) (.classMem (.cv y) D)) ps x p0002 hyp_vtocl2gaf_1
  have p0004 :=
    @gNfel1 y A C
      (by
        aesop)
      hyp_vtocl2gaf_b
  have p0005 :=
    @gNfel1 y B D
      (by
        aesop)
      hyp_vtocl2gaf_c
  have p0006 := @gNfan (.classMem A C) (.classMem B D) y p0004 p0005
  have p0007 :=
    @gNfim (synWa (.classMem A C) (.classMem B D)) ch y p0006 hyp_vtocl2gaf_2
  have p0008 := @gEleq1 (.cv x) A C
  have p0009 :=
    @gAnbi1d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C)
      (.classMem (.cv y) D) p0008
  have p0010 :=
    @gImbi12d (.classEq (.cv x) A) (synWa (.classMem (.cv x) C) (.classMem (.cv y) D))
      (synWa (.classMem A C) (.classMem (.cv y) D)) ph ps p0009 hyp_vtocl2gaf_3
  have p0011 := @gEleq1 (.cv y) B D
  have p0012 :=
    @gAnbi2d (.classEq (.cv y) B) (.classMem (.cv y) D) (.classMem B D) (.classMem A C)
      p0011
  have p0013 :=
    @gImbi12d (.classEq (.cv y) B) (synWa (.classMem A C) (.classMem (.cv y) D))
      (synWa (.classMem A C) (.classMem B D)) ps ch p0012 hyp_vtocl2gaf_4
  have p0014 :=
    @gVtocl2gf (.imp (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)) ph)
      (.imp (synWa (.classMem A C) (.classMem (.cv y) D)) ps)
      (.imp (synWa (.classMem A C) (.classMem B D)) ch) x y A B C D hyp_vtocl2gaf_a
      hyp_vtocl2gaf_b hyp_vtocl2gaf_c p0003 p0007 p0010 p0013 hyp_vtocl2gaf_5
  have p0015 := @gPm243i (synWa (.classMem A C) (.classMem B D)) ch p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_vtocl2ga`. -/
@[expose]
noncomputable def gVtocl2ga (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_ch_y : y ∉ ch.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_vtocl2ga_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtocl2ga_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch)))
    (hyp_vtocl2ga_3 :
      Nominal.NPrf (.imp (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)) ph)) :
    Nominal.NPrf (.imp (synWa (.classMem A C) (.classMem B D)) ch) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfcv y A
      (by
        aesop)
  have p0002 :=
    @gNfcv y B
      (by
        aesop)
  have p0003 :=
    @gNfv ps x
      (by
        aesop)
  have p0004 :=
    @gNfv ch y
      (by
        aesop)
  have p0005 :=
    @gVtocl2gaf ph ps ch x y A B C D
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      p0000 p0001 p0002 p0003 p0004 hyp_vtocl2ga_1 hyp_vtocl2ga_2 hyp_vtocl2ga_3
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_vtocleg`. -/
@[expose]
noncomputable def gVtocleg (ph : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_vtocleg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) ph)) :
    Nominal.NPrf (.imp (.classMem A V) ph) :=
  by
  have p0000 :=
    @gElisset x A V
      (by
        aesop)
  have p0001 :=
    @gExlimiv (.classEq (.cv x) A) ph x
      (by
        aesop)
      hyp_vtocleg_1
  have p0002 := @gSyl (.classMem A V) (synWex x (.classEq (.cv x) A)) ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_spcimgft`. -/
@[expose]
noncomputable def gSpcimgft (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_spcimgft_1 : Nominal.NPrf (synWnf x ps))
    (hyp_spcimgft_2 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf
      (.imp (.all x (.imp (.classEq (.cv x) A) (.imp ph ps)))
        (.imp (.classMem A B) (.imp (.all x ph) ps))) :=
  by
  have p0000 := @gElex A B
  have p0001 := @gIssetf x A hyp_spcimgft_2
  have p0002 := @gExim (.classEq (.cv x) A) (.imp ph ps) x
  have p0003 :=
    @gSyl5bi (.classMem A (synCvv)) (synWex x (.classEq (.cv x) A))
      (.all x (.imp (.classEq (.cv x) A) (.imp ph ps))) (synWex x (.imp ph ps)) p0001
      p0002
  have p0004 := @gN1936 ph ps x hyp_spcimgft_1
  have p0005 :=
    @gSyl6ib (.all x (.imp (.classEq (.cv x) A) (.imp ph ps))) (.classMem A (synCvv))
      (synWex x (.imp ph ps)) (.imp (.all x ph) ps) p0003 p0004
  have p0006 :=
    @gSyl5 (.classMem A B) (.classMem A (synCvv))
      (.all x (.imp (.classEq (.cv x) A) (.imp ph ps))) (.imp (.all x ph) ps) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_spcgft`. -/
@[expose]
noncomputable def gSpcgft (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_spcimgft_1 : Nominal.NPrf (synWnf x ps))
    (hyp_spcimgft_2 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf
      (.imp (.all x (.imp (.classEq (.cv x) A) (synWb ph ps)))
        (.imp (.classMem A B) (.imp (.all x ph) ps))) :=
  by
  have p0000 := @gBi1 ph ps
  have p0001 := @gImim2i (synWb ph ps) (.imp ph ps) (.classEq (.cv x) A) p0000
  have p0002 :=
    @gAlimi (.imp (.classEq (.cv x) A) (synWb ph ps))
      (.imp (.classEq (.cv x) A) (.imp ph ps)) x p0001
  have p0003 := @gSpcimgft ph ps x A B hyp_spcimgft_1 hyp_spcimgft_2
  have p0004 :=
    @gSyl (.all x (.imp (.classEq (.cv x) A) (synWb ph ps)))
      (.all x (.imp (.classEq (.cv x) A) (.imp ph ps)))
      (.imp (.classMem A B) (.imp (.all x ph) ps)) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_spcgf`. -/
@[expose]
noncomputable def gSpcgf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (hyp_spcgf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_spcgf_2 : Nominal.NPrf (synWnf x ps))
    (hyp_spcgf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (.imp (.all x ph) ps)) :=
  by
  have p0000 := @gSpcgft ph ps x A V hyp_spcgf_2 hyp_spcgf_1
  have p0001 :=
    @gMpg (.imp (.classEq (.cv x) A) (synWb ph ps))
      (.imp (.classMem A V) (.imp (.all x ph) ps)) x p0000 hyp_spcgf_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_spcegf`. -/
@[expose]
noncomputable def gSpcegf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (hyp_spcgf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_spcgf_2 : Nominal.NPrf (synWnf x ps))
    (hyp_spcgf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (.imp ps (synWex x ph))) :=
  by
  have p0000 := @gNfn ps x hyp_spcgf_2
  have p0001 := @gNotbid (.classEq (.cv x) A) ph ps hyp_spcgf_3
  have p0002 := @gSpcgf (.neg ph) (.neg ps) x A V hyp_spcgf_1 p0000 p0001
  have p0003 := @gCon2d (.classMem A V) (.all x (.neg ph)) ps p0002
  have p0004 := (Nominal.biimpRefl (synWex x ph))
  have p0005 :=
    @gSyl6ibr (.classMem A V) ps (.neg (.all x (.neg ph))) (synWex x ph) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_spcimdv`. -/
@[expose]
noncomputable def gSpcimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_spcimdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_spcimdv_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) ch)) :=
  by
  have p0000 := @gEx ph (.classEq (.cv x) A) (.imp ps ch) hyp_spcimdv_2
  have p0001 :=
    @gAlrimiv ph (.imp (.classEq (.cv x) A) (.imp ps ch)) x
      (by
        aesop)
      p0000
  have p0002 :=
    @gNfv ch x
      (by
        aesop)
  have p0003 :=
    @gNfcv x A
      (by
        aesop)
  have p0004 := @gSpcimgft ps ch x A B p0002 p0003
  have p0005 :=
    @gSylc ph (.all x (.imp (.classEq (.cv x) A) (.imp ps ch))) (.classMem A B)
      (.imp (.all x ps) ch) p0001 hyp_spcimdv_1 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_spcimedv`. -/
@[expose]
noncomputable def gSpcimedv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_spcimdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_spcimedv_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (.imp ch ps))) :
    Nominal.NPrf (.imp ph (.imp ch (synWex x ps))) :=
  by
  have p0000 := @gCon3d (synWa ph (.classEq (.cv x) A)) ch ps hyp_spcimedv_2
  have p0001 :=
    @gSpcimdv ph (.neg ps) (.neg ch) x A B
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        aesop)
      hyp_spcimdv_1 p0000
  have p0002 := @gCon2d ph (.all x (.neg ps)) ch p0001
  have p0003 := (Nominal.biimpRefl (synWex x ps))
  have p0004 := @gSyl6ibr ph ch (.neg (.all x (.neg ps))) (synWex x ps) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_spcgv`. -/
@[expose]
noncomputable def gSpcgv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_spcgv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (.imp (.all x ph) ps)) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfv ps x
      (by
        aesop)
  have p0002 := @gSpcgf ph ps x A V p0000 p0001 hyp_spcgv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_spcegv`. -/
@[expose]
noncomputable def gSpcegv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_spcgv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (.imp ps (synWex x ph))) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfv ps x
      (by
        aesop)
  have p0002 := @gSpcegf ph ps x A V p0000 p0001 hyp_spcgv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_spc2egv`. -/
@[expose]
noncomputable def gSpc2egv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_spc2egv_1 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.imp ps (synWex x (synWex y ph)))) :=
  by
  have p0000 :=
    @gElisset x A V
      (by
        aesop)
  have p0001 :=
    @gElisset y B W
      (by
        aesop)
  have p0002 :=
    @gAnim12i (.classMem A V) (synWex x (.classEq (.cv x) A)) (.classMem B W)
      (synWex y (.classEq (.cv y) B)) p0000 p0001
  have p0003 :=
    @gEeanv (.classEq (.cv x) A) (.classEq (.cv y) B) x y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0004 :=
    @gSylibr (synWa (.classMem A V) (.classMem B W))
      (synWa (synWex x (.classEq (.cv x) A)) (synWex y (.classEq (.cv y) B)))
      (synWex x (synWex y (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)))) p0002
      p0003
  have p0005 :=
    @gBiimprcd (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph ps hyp_spc2egv_1
  have p0006 :=
    @gN2eximdv ps (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph x y
      (by
        aesop)
      (by
        aesop)
      p0005
  have p0007 :=
    @gSyl5com (synWa (.classMem A V) (.classMem B W))
      (synWex x (synWex y (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)))) ps
      (synWex x (synWex y ph)) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_spc2gv`. -/
@[expose]
noncomputable def gSpc2gv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_spc2egv_1 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.imp (.all x (.all y ph)) ps)) :=
  by
  have p0000 :=
    @gNotbid (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph ps hyp_spc2egv_1
  have p0001 :=
    @gSpc2egv (.neg ph) (.neg ps) x y A B V W
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        aesop)
      p0000
  have p0002 := @gN2nalexn ph x y
  have p0003 :=
    @gSyl6ibr (synWa (.classMem A V) (.classMem B W)) (.neg ps)
      (synWex x (synWex y (.neg ph))) (.neg (.all x (.all y ph))) p0001 p0002
  have p0004 :=
    @gCon4d (synWa (.classMem A V) (.classMem B W)) ps (.all x (.all y ph)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_spc3egv`. -/
@[expose]
noncomputable def gSpc3egv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (X : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_spc3egv_1 : Nominal.NPrf
        (.imp (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
        (.imp ps (synWex x (synWex y (synWex z ph))))) :=
  by
  have p0000 :=
    @gElisset x A V
      (by
        aesop)
  have p0001 :=
    @gElisset y B W
      (by
        aesop)
  have p0002 :=
    @gElisset z C X
      (by
        aesop)
  have p0003 :=
    @gN3anim123i (.classMem A V) (synWex x (.classEq (.cv x) A)) (.classMem B W)
      (synWex y (.classEq (.cv y) B)) (.classMem C X) (synWex z (.classEq (.cv z) C))
      p0000 p0001 p0002
  have p0004 :=
    @gEeeanv (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C) x y z
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      (by
        aesop)
  have p0005 :=
    @gSylibr (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
      (synW3a (synWex x (.classEq (.cv x) A)) (synWex y (.classEq (.cv y) B))
        (synWex z (.classEq (.cv z) C)))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      p0003 p0004
  have p0006 :=
    @gBiimprcd (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      ph ps hyp_spc3egv_1
  have p0007 :=
    @gEximdv ps (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      ph z
      (by
        aesop)
      p0006
  have p0008 :=
    @gN2eximdv ps
      (synWex z (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))
      (synWex z ph) x y
      (by
        aesop)
      (by
        aesop)
      p0007
  have p0009 :=
    @gSyl5com (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      ps (synWex x (synWex y (synWex z ph))) p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_spc3gv`. -/
@[expose]
noncomputable def gSpc3gv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (V : Class) (W : Class) (X : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_spc3egv_1 : Nominal.NPrf
        (.imp (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
        (.imp (.all x (.all y (.all z ph))) ps)) :=
  by
  have p0000 :=
    @gNotbid (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph
      ps hyp_spc3egv_1
  have p0001 :=
    @gSpc3egv (.neg ph) (.neg ps) x y z A B C V W X
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      p0000
  have p0002 := @gExnal ph z
  have p0003 := @gExbii (synWex z (.neg ph)) (.neg (.all z ph)) y p0002
  have p0004 := @gExnal (.all z ph) y
  have p0005 :=
    @gBitri (synWex y (synWex z (.neg ph))) (synWex y (.neg (.all z ph)))
      (.neg (.all y (.all z ph))) p0003 p0004
  have p0006 :=
    @gExbii (synWex y (synWex z (.neg ph))) (.neg (.all y (.all z ph))) x p0005
  have p0007 := @gExnal (.all y (.all z ph)) x
  have p0008 :=
    @gBitr2i (synWex x (synWex y (synWex z (.neg ph))))
      (synWex x (.neg (.all y (.all z ph)))) (.neg (.all x (.all y (.all z ph)))) p0006
      p0007
  have p0009 :=
    @gSyl6ibr (synW3a (.classMem A V) (.classMem B W) (.classMem C X)) (.neg ps)
      (synWex x (synWex y (synWex z (.neg ph)))) (.neg (.all x (.all y (.all z ph))))
      p0001 p0008
  have p0010 :=
    @gCon4d (synW3a (.classMem A V) (.classMem B W) (.classMem C X)) ps
      (.all x (.all y (.all z ph))) p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_spcv`. -/
@[expose]
noncomputable def gSpcv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_spcv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_spcv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  have p0000 :=
    @gSpcgv ph ps x A (synCvv)
      (by
        aesop)
      (by
        aesop)
      hyp_spcv_2
  have p0001 := Nominal.mp hyp_spcv_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_spcev`. -/
@[expose]
noncomputable def gSpcev (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_spcv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_spcv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp ps (synWex x ph)) :=
  by
  have p0000 :=
    @gSpcegv ph ps x A (synCvv)
      (by
        aesop)
      (by
        aesop)
      hyp_spcv_2
  have p0001 := Nominal.mp hyp_spcv_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_spc2ev`. -/
@[expose]
noncomputable def gSpc2ev (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_spc2ev_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_spc2ev_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_spc2ev_3 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps))) :
    Nominal.NPrf (.imp ps (synWex x (synWex y ph))) :=
  by
  have p0000 :=
    @gSpc2egv ph ps x y A B (synCvv) (synCvv)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      hyp_spc2ev_3
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.imp ps (synWex x (synWex y ph))) hyp_spc2ev_1 hyp_spc2ev_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspc`. -/
@[expose]
noncomputable def gRspc (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_rspc_1 : Nominal.NPrf (synWnf x ps))
    (hyp_rspc_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A B) (.imp (synWral x B ph) ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x B ph))
  have p0001 :=
    @gNfcv x A
      (by
        aesop)
  have p0002 :=
    @gNfv (.classMem A B) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
  have p0003 := @gNfim (.classMem A B) ps x p0002 hyp_rspc_1
  have p0004 := @gEleq1 (.cv x) A B
  have p0005 :=
    @gImbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0004
      hyp_rspc_2
  have p0006 :=
    @gSpcgf (.imp (.classMem (.cv x) B) ph) (.imp (.classMem A B) ps) x A B p0001 p0003
      p0005
  have p0007 :=
    @gPm243a (.all x (.imp (.classMem (.cv x) B) ph)) (.classMem A B) ps p0006
  have p0008 :=
    @gSyl5bi (synWral x B ph) (.all x (.imp (.classMem (.cv x) B) ph)) (.classMem A B)
      ps p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_rspce`. -/
@[expose]
noncomputable def gRspce (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_rspc_1 : Nominal.NPrf (synWnf x ps))
    (hyp_rspc_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (synWa (.classMem A B) ps) (synWrex x B ph)) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfv (.classMem A B) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
  have p0002 := @gNfan (.classMem A B) ps x p0001 hyp_rspc_1
  have p0003 := @gEleq1 (.cv x) A B
  have p0004 :=
    @gAnbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0003
      hyp_rspc_2
  have p0005 :=
    @gSpcegf (synWa (.classMem (.cv x) B) ph) (synWa (.classMem A B) ps) x A B p0000
      p0002 p0004
  have p0006 :=
    @gAnabsi5 (.classMem A B) ps (synWex x (synWa (.classMem (.cv x) B) ph)) p0005
  have p0007 := (Nominal.biimpRefl (synWrex x B ph))
  have p0008 :=
    @gSylibr (synWa (.classMem A B) ps) (synWex x (synWa (.classMem (.cv x) B) ph))
      (synWrex x B ph) p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_rspcv`. -/
@[expose]
noncomputable def gRspcv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A B) (.imp (synWral x B ph) ps)) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 :=
    @gRspc ph ps x A B
      (by
        aesop)
      (by
        aesop)
      p0000 hyp_rspcv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspccv`. -/
@[expose]
noncomputable def gRspccv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (synWral x B ph) (.imp (.classMem A B) ps)) :=
  by
  have p0000 :=
    @gRspcv ph ps x A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      hyp_rspcv_1
  have p0001 := @gCom12 (.classMem A B) (synWral x B ph) ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspcva`. -/
@[expose]
noncomputable def gRspcva (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (synWa (.classMem A B) (synWral x B ph)) ps) :=
  by
  have p0000 :=
    @gRspcv ph ps x A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      hyp_rspcv_1
  have p0001 := @gImp (.classMem A B) (synWral x B ph) ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspccva`. -/
@[expose]
noncomputable def gRspccva (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (synWa (synWral x B ph) (.classMem A B)) ps) :=
  by
  have p0000 :=
    @gRspcv ph ps x A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      hyp_rspcv_1
  have p0001 := @gImpcom (.classMem A B) (synWral x B ph) ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspcev`. -/
@[expose]
noncomputable def gRspcev (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_rspcv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (synWa (.classMem A B) ps) (synWrex x B ph)) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 :=
    @gRspce ph ps x A B
      (by
        aesop)
      (by
        aesop)
      p0000 hyp_rspcv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspcimdv`. -/
@[expose]
noncomputable def gRspcimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_x : x ∉ ph.fv) (hyp_rspcimdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_rspcimdv_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWral x B ps) ch)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWral x B ps))
  have p0001 := @gSimpr ph (.classEq (.cv x) A)
  have p0002 := @gEleq1d (synWa ph (.classEq (.cv x) A)) (.cv x) A B p0001
  have p0003 :=
    @gBiimprd (synWa ph (.classEq (.cv x) A)) (.classMem (.cv x) B) (.classMem A B)
      p0002
  have p0004 :=
    @gImim12d (synWa ph (.classEq (.cv x) A)) (.classMem A B) (.classMem (.cv x) B) ps
      ch p0003 hyp_rspcimdv_2
  have p0005 :=
    @gSpcimdv ph (.imp (.classMem (.cv x) B) ps) (.imp (.classMem A B) ch) x A B
      (by
        aesop)
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union] at ⊢;
            aesop))
      (by
        aesop)
      hyp_rspcimdv_1 p0004
  have p0006 :=
    @gMpid ph (.all x (.imp (.classMem (.cv x) B) ps)) (.classMem A B) ch hyp_rspcimdv_1
      p0005
  have p0007 :=
    @gSyl5bi (synWral x B ps) (.all x (.imp (.classMem (.cv x) B) ps)) ph ch p0000 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay
