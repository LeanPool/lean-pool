/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk006
public import LeanPool.NFWeakPartition.ReplaySupport.FreshSubstitution

/-! NF weak partition development: NominalWPPReplayChunk007. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_rspcimedv`. -/
@[expose]
noncomputable def gRspcimedv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_x : x ∉ ph.fv) (hyp_rspcimdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_rspcimedv_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (.imp ch ps))) :
    Nominal.NPrf (.imp ph (.imp ch (synWrex x B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @gCon3d (synWa ph (.classEq (.cv x) A)) ch ps hyp_rspcimedv_2
  have p0001 :=
    @gRspcimdv ph (.neg ps) (.neg ch) x A B
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
        | (aesop))
      hyp_rspcimdv_1 p0000
  have p0002 := @gCon2d ph (synWral x B (.neg ps)) ch p0001
  have p0003 := @gDfrex2 ps x B
  have p0004 :=
    @gSyl6ibr ph ch (.neg (synWral x B (.neg ps))) (synWrex x B ps) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_rspcdv`. -/
@[expose]
noncomputable def gRspcdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_x : x ∉ ph.fv) (hyp_rspcdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_rspcdv_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWral x B ps) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @gBiimpd (synWa ph (.classEq (.cv x) A)) ps ch hyp_rspcdv_2
  have p0001 :=
    @gRspcimdv ph ps ch x A B
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
      hyp_rspcdv_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspcedv`. -/
@[expose]
noncomputable def gRspcedv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_x : x ∉ ph.fv) (hyp_rspcdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_rspcdv_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.imp ch (synWrex x B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @gBiimprd (synWa ph (.classEq (.cv x) A)) ps ch hyp_rspcdv_2
  have p0001 :=
    @gRspcimedv ph ps ch x A B
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
      hyp_rspcdv_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspc2`. -/
@[expose]
noncomputable def gRspc2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv)
    (dv_x_y : x ≠ y) (hyp_rspc2_1 : Nominal.NPrf (synWnf x ch))
    (hyp_rspc2_2 : Nominal.NPrf (synWnf y ps))
    (hyp_rspc2_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ch)))
    (hyp_rspc2_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ch ps))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D))
        (.imp (synWral x C (synWral y D ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @gNfcv x D
      (by
        first
        | (aesop))
  have p0001 := @gNfral ch x y D p0000 hyp_rspc2_1
  have p0002 :=
    @gRalbidv (.classEq (.cv x) A) ph ch y D
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
      hyp_rspc2_3
  have p0003 :=
    @gRspc (synWral y D ph) (synWral y D ch) x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0001 p0002
  have p0004 :=
    @gRspc ch ps y B D
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_rspc2_2 hyp_rspc2_4
  have p0005 :=
    @gSylan9 (.classMem A C) (synWral x C (synWral y D ph)) (synWral y D ch)
      (.classMem B D) ps p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_rspc2v`. -/
@[expose]
noncomputable def gRspc2v (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_rspc2v_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ch)))
    (hyp_rspc2v_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ch ps))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D))
        (.imp (synWral x C (synWral y D ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @gNfv ch x
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ps y
      (by
        first
        | (aesop))
  have p0002 :=
    @gRspc2 ph ps ch x y A B C D
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
      p0000 p0001 hyp_rspc2v_1 hyp_rspc2v_2
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rspc2va`. -/
@[expose]
noncomputable def gRspc2va (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_rspc2v_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ch)))
    (hyp_rspc2v_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ch ps))) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem A C) (.classMem B D)) (synWral x C (synWral y D ph)))
        ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @gRspc2v ph ps ch x y A B C D
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
      hyp_rspc2v_1 hyp_rspc2v_2
  have p0001 :=
    @gImp (synWa (.classMem A C) (.classMem B D)) (synWral x C (synWral y D ph)) ps
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rspc2ev`. -/
@[expose]
noncomputable def gRspc2ev (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_rspc2v_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ch)))
    (hyp_rspc2v_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ch ps))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A C) (.classMem B D) ps) (synWrex x C (synWrex y D ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @gRspcev ch ps y B D
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_rspc2v_2
  have p0001 :=
    @gAnim2i (synWa (.classMem B D) ps) (synWrex y D ch) (.classMem A C) p0000
  have p0002 :=
    @gN3impb (.classMem A C) (.classMem B D) ps
      (synWa (.classMem A C) (synWrex y D ch)) p0001
  have p0003 :=
    @gRexbidv (.classEq (.cv x) A) ph ch y D
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
      hyp_rspc2v_1
  have p0004 :=
    @gRspcev (synWrex y D ph) (synWrex y D ch) x A C
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
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      p0003
  have p0005 :=
    @gSyl (synW3a (.classMem A C) (.classMem B D) ps)
      (synWa (.classMem A C) (synWrex y D ch)) (synWrex x C (synWrex y D ph)) p0002
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_rspc3v`. -/
@[expose]
noncomputable def gRspc3v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) (T : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_y : y ∉ B.fv)
    (dv_B_z : z ∉ B.fv) (dv_C_z : z ∉ C.fv) (dv_R_x : x ∉ R.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_T_x : x ∉ T.fv) (dv_T_y : y ∉ T.fv) (dv_T_z : z ∉ T.fv)
    (dv_ch_x : x ∉ ch.fv) (dv_ps_z : z ∉ ps.fv) (dv_th_y : y ∉ th.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_rspc3v_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ch)))
    (hyp_rspc3v_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ch th)))
    (hyp_rspc3v_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (synWb th ps))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A R) (.classMem B S) (.classMem C T))
        (.imp (synWral x R (synWral y S (synWral z T ph))) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
                  ({ z } : Finset Var) ∪
                A.fv ∪
              B.fv ∪
            C.fv ∪
          R.fv ∪
        S.fv ∪
      T.fv
  have p0000 :=
    @gRalbidv (.classEq (.cv x) A) ph ch z T
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
      hyp_rspc3v_1
  have p0001 :=
    @gRalbidv (.classEq (.cv y) B) ch th z T
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
      hyp_rspc3v_2
  have p0002 :=
    @gRspc2v (synWral z T ph) (synWral z T th) (synWral z T ch) x y A B R S
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
      (by
        first
        | (aesop))
      p0000 p0001
  have p0003 :=
    @gRspcv th ps z C T
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_rspc3v_3
  have p0004 :=
    @gSylan9 (synWa (.classMem A R) (.classMem B S))
      (synWral x R (synWral y S (synWral z T ph))) (synWral z T th) (.classMem C T) ps
      p0002 p0003
  have p0005 :=
    @gN3impa (.classMem A R) (.classMem B S) (.classMem C T)
      (.imp (synWral x R (synWral y S (synWral z T ph))) ps) p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_eqvinc`. -/
@[expose]
noncomputable def gEqvinc (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_eqvinc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.classEq A B) (synWex x (synWa (.classEq (.cv x) A) (.classEq (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gIsseti x A
      (by
        first
        | (aesop))
      hyp_eqvinc_1
  have p0001 := Nominal.ax1 (.classEq (.cv x) A) (.classEq A B)
  have p0002 := @gEqtr (.cv x) A B
  have p0003 := @gEx (.classEq (.cv x) A) (.classEq A B) (.classEq (.cv x) B) p0002
  have p0004 :=
    @gJca (.classEq (.cv x) A) (.imp (.classEq A B) (.classEq (.cv x) A))
      (.imp (.classEq A B) (.classEq (.cv x) B)) p0001 p0003
  have p0005 :=
    @gEximi (.classEq (.cv x) A)
      (synWa (.imp (.classEq A B) (.classEq (.cv x) A))
        (.imp (.classEq A B) (.classEq (.cv x) B)))
      x p0004
  have p0006 := @gPm343 (.classEq A B) (.classEq (.cv x) A) (.classEq (.cv x) B)
  have p0007 :=
    @gEximi
      (synWa (.imp (.classEq A B) (.classEq (.cv x) A))
        (.imp (.classEq A B) (.classEq (.cv x) B)))
      (.imp (.classEq A B) (synWa (.classEq (.cv x) A) (.classEq (.cv x) B))) x p0006
  have p0008 :=
    @gMp2b (synWex x (.classEq (.cv x) A))
      (synWex x (synWa (.imp (.classEq A B) (.classEq (.cv x) A))
          (.imp (.classEq A B) (.classEq (.cv x) B))))
      (synWex x (.imp (.classEq A B) (synWa (.classEq (.cv x) A) (.classEq (.cv x) B))))
      p0000 p0005 p0007
  have p0009 :=
    @gN1937aiv (.classEq A B) (synWa (.classEq (.cv x) A) (.classEq (.cv x) B)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0008
  have p0010 := @gEqtr2 (.cv x) A B
  have p0011 :=
    @gExlimiv (synWa (.classEq (.cv x) A) (.classEq (.cv x) B)) (.classEq A B) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0010
  have p0012 :=
    @gImpbii (.classEq A B)
      (synWex x (synWa (.classEq (.cv x) A) (.classEq (.cv x) B))) p0009 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_alexeq`. -/
@[expose]
noncomputable def gAlexeq (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_alexeq_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.all x (.imp (.classEq (.cv x) A) ph))
        (synWex x (synWa (.classEq (.cv x) A) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gEqeq2 (.cv y) A (.cv x)
  have p0001 :=
    @gAnbi1d (.classEq (.cv y) A) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) A) ph
      p0000
  have p0002 :=
    @gExbidv (.classEq (.cv y) A) (synWa (.classEq (.cv x) (.cv y)) ph)
      (synWa (.classEq (.cv x) A) ph) x
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
      p0001
  have p0003 :=
    @gImbi1d (.classEq (.cv y) A) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) A) ph
      p0000
  have p0004 :=
    @gAlbidv (.classEq (.cv y) A) (.imp (.classEq (.cv x) (.cv y)) ph)
      (.imp (.classEq (.cv x) A) ph) x
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
      p0003
  have p0005 :=
    @gSb56 ph x y
      (by
        first
        | (aesop))
  have p0006_e03_recanon :
    Nominal.NPrf
      (synWb (synWex x (synWa (.classEq (.cv x) (.cv y)) ph))
        (.all x (.imp (.classEq (.cv x) (.cv y)) ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gVtoclb (synWex x (synWa (.classEq (.cv x) (.cv y)) ph))
      (.all x (.imp (.classEq (.cv x) (.cv y)) ph))
      (synWex x (synWa (.classEq (.cv x) A) ph)) (.all x (.imp (.classEq (.cv x) A) ph))
      y A
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      hyp_alexeq_1 p0002 p0004 p0006_e03_recanon
  have p0007 :=
    @gBicomi (synWex x (synWa (.classEq (.cv x) A) ph))
      (.all x (.imp (.classEq (.cv x) A) ph)) p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ceqex`. -/
@[expose]
noncomputable def gCeqex (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classEq (.cv x) A) (synWb ph (synWex x (synWa (.classEq (.cv x) A) ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gN198a (.classEq (.cv x) A) x
  have p0001 :=
    @gIsset x A
      (by
        first
        | (aesop))
  have p0002 :=
    @gSylibr (.classEq (.cv x) A) (synWex x (.classEq (.cv x) A))
      (.classMem A (synCvv)) p0000 p0001
  have p0003 := @gEqeq2 (.cv y) A (.cv x)
  have p0004 :=
    @gAnbi1d (.classEq (.cv y) A) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) A) ph
      p0003
  have p0005 :=
    @gExbidv (.classEq (.cv y) A) (synWa (.classEq (.cv x) (.cv y)) ph)
      (synWa (.classEq (.cv x) A) ph) x
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
      p0004
  have p0006 :=
    @gBibi2d (.classEq (.cv y) A) (synWex x (synWa (.classEq (.cv x) (.cv y)) ph))
      (synWex x (synWa (.classEq (.cv x) A) ph)) ph p0005
  have p0007 :=
    @gImbi12d (.classEq (.cv y) A) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) A)
      (synWb ph (synWex x (synWa (.classEq (.cv x) (.cv y)) ph)))
      (synWb ph (synWex x (synWa (.classEq (.cv x) A) ph))) p0003 p0006
  have p0008 := @gN198a (synWa (.classEq (.cv x) (.cv y)) ph) x
  have p0009 :=
    @gEx (.classEq (.cv x) (.cv y)) ph (synWex x (synWa (.classEq (.cv x) (.cv y)) ph))
      p0008
  have p0010 := @gVex y
  have p0011 :=
    @gAlexeq ph x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0010
  have p0012 := @gSp (.imp (.classEq (.cv x) (.cv y)) ph) x
  have p0013 :=
    @gCom12 (.all x (.imp (.classEq (.cv x) (.cv y)) ph)) (.classEq (.cv x) (.cv y)) ph
      p0012
  have p0014 :=
    @gSyl5bir (synWex x (synWa (.classEq (.cv x) (.cv y)) ph))
      (.all x (.imp (.classEq (.cv x) (.cv y)) ph)) (.classEq (.cv x) (.cv y)) ph p0011
      p0013
  have p0015 :=
    @gImpbid (.classEq (.cv x) (.cv y)) ph
      (synWex x (synWa (.classEq (.cv x) (.cv y)) ph)) p0009 p0014
  have p0016 :=
    @gVtoclg
      (.imp (.classEq (.cv x) (.cv y))
        (synWb ph (synWex x (synWa (.classEq (.cv x) (.cv y)) ph))))
      (.imp (.classEq (.cv x) A) (synWb ph (synWex x (synWa (.classEq (.cv x) A) ph))))
      y A (synCvv)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      p0007 p0015
  have p0017 :=
    @gMpcom (.classMem A (synCvv)) (.classEq (.cv x) A)
      (synWb ph (synWex x (synWa (.classEq (.cv x) A) ph))) p0002 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_ceqsexg`. -/
@[expose]
noncomputable def gCeqsexg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (hyp_ceqsexg_1 : Nominal.NPrf (synWnf x ps))
    (hyp_ceqsexg_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (synWex x (synWa (.classEq (.cv x) A) ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 := @gNfe1 (synWa (.classEq (.cv x) A) ph) x
  have p0002 :=
    @gNfbi (synWex x (synWa (.classEq (.cv x) A) ph)) ps x p0001 hyp_ceqsexg_1
  have p0003 :=
    @gCeqex ph x A
      (by
        first
        | (aesop))
  have p0004 :=
    @gBibi12d (.classEq (.cv x) A) ph (synWex x (synWa (.classEq (.cv x) A) ph)) ph ps
      p0003 hyp_ceqsexg_2
  have p0005 := @gBiid ph
  have p0006 :=
    @gVtoclgf (synWb ph ph) (synWb (synWex x (synWa (.classEq (.cv x) A) ph)) ps) x A
      V p0000 p0002 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ceqsexgv`. -/
@[expose]
noncomputable def gCeqsexgv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsexgv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (synWex x (synWa (.classEq (.cv x) A) ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @gCeqsexg ph ps x A V
      (by
        first
        | (aesop))
      p0000 hyp_ceqsexgv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ceqsrexv`. -/
@[expose]
noncomputable def gCeqsrexv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsrexv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (.classMem A B) (synWb (synWrex x B (synWa (.classEq (.cv x) A) ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := (Nominal.biimpRefl (synWrex x B (synWa (.classEq (.cv x) A) ph)))
  have p0001 := @gAn12 (.classEq (.cv x) A) (.classMem (.cv x) B) ph
  have p0002 :=
    @gExbii (synWa (.classEq (.cv x) A) (synWa (.classMem (.cv x) B) ph))
      (synWa (.classMem (.cv x) B) (synWa (.classEq (.cv x) A) ph)) x p0001
  have p0003 :=
    @gBitr4i (synWrex x B (synWa (.classEq (.cv x) A) ph))
      (synWex x (synWa (.classMem (.cv x) B) (synWa (.classEq (.cv x) A) ph)))
      (synWex x (synWa (.classEq (.cv x) A) (synWa (.classMem (.cv x) B) ph))) p0000
      p0002
  have p0004 := @gEleq1 (.cv x) A B
  have p0005 :=
    @gAnbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0004
      hyp_ceqsrexv_1
  have p0006 :=
    @gCeqsexgv (synWa (.classMem (.cv x) B) ph) (synWa (.classMem A B) ps) x A B
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
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union] at ⊢;
            aesop))
      p0005
  have p0007 :=
    @gBianabs (.classMem A B)
      (synWex x (synWa (.classEq (.cv x) A) (synWa (.classMem (.cv x) B) ph))) ps p0006
  have p0008 :=
    @gSyl5bb (synWrex x B (synWa (.classEq (.cv x) A) ph))
      (synWex x (synWa (.classEq (.cv x) A) (synWa (.classMem (.cv x) B) ph)))
      (.classMem A B) ps p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_clel2`. -/
@[expose]
noncomputable def gClel2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_clel2_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem A B) (.all x (.imp (.classEq (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @gEleq1 (.cv x) A B
  have p0001 :=
    @gCeqsalv (.classMem (.cv x) B) (.classMem A B) x A
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
              Finset.mem_union] at ⊢;
            aesop))
      hyp_clel2_1 p0000
  have p0002 :=
    @gBicomi (.all x (.imp (.classEq (.cv x) A) (.classMem (.cv x) B))) (.classMem A B)
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_clel3g`. -/
@[expose]
noncomputable def gClel3g (x : Var) (A : Class) (B : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem B V) (synWb (.classMem A B)
          (synWex x (synWa (.classEq (.cv x) B) (.classMem A (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  have p0000 := @gEleq2 (.cv x) B A
  have p0001 :=
    @gCeqsexgv (.classMem A (.cv x)) (.classMem A B) x B V
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
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    @gBicomd (.classMem B V)
      (synWex x (synWa (.classEq (.cv x) B) (.classMem A (.cv x)))) (.classMem A B)
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_clel3`. -/
@[expose]
noncomputable def gClel3 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_clel3_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem A B)
        (synWex x (synWa (.classEq (.cv x) B) (.classMem A (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gClel3g x A B (synCvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := Nominal.mp hyp_clel3_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elabgf`. -/
@[expose]
noncomputable def gElabgf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_elabgf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_elabgf_2 : Nominal.NPrf (synWnf x ps))
    (hyp_elabgf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A B) (synWb (.classMem A (.cab x ph)) ps)) :=
  by
  have p0000 := @gNfab1 ph x
  have p0001 := @gNfel x A (.cab x ph) hyp_elabgf_1 p0000
  have p0002 := @gNfbi (.classMem A (.cab x ph)) ps x p0001 hyp_elabgf_2
  have p0003 := @gEleq1 (.cv x) A (.cab x ph)
  have p0004 :=
    @gBibi12d (.classEq (.cv x) A) (.classMem (.cv x) (.cab x ph))
      (.classMem A (.cab x ph)) ph ps p0003 hyp_elabgf_3
  have p0005 := @gAbid ph x
  have p0006 :=
    @gVtoclgf (synWb (.classMem (.cv x) (.cab x ph)) ph)
      (synWb (.classMem A (.cab x ph)) ps) x A B hyp_elabgf_1 p0002 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_elabf`. -/
@[expose]
noncomputable def gElabf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_elabf_1 : Nominal.NPrf (synWnf x ps))
    (hyp_elabf_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_elabf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.classMem A (.cab x ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 := @gElabgf ph ps x A (synCvv) p0000 hyp_elabf_1 hyp_elabf_3
  have p0002 := Nominal.mp hyp_elabf_2 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elab`. -/
@[expose]
noncomputable def gElab (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_elab_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_elab_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.classMem A (.cab x ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @gElabf ph ps x A
      (by
        first
        | (aesop))
      p0000 hyp_elab_1 hyp_elab_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elabg`. -/
@[expose]
noncomputable def gElabg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (synWb (.classMem A (.cab x ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0002 := @gElabgf ph ps x A V p0000 p0001 hyp_elabg_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elab2g`. -/
@[expose]
noncomputable def gElab2g (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (V : Class) (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elab2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_elab2g_2 : Nominal.NPrf (.classEq B (.cab x ph))) :
    Nominal.NPrf (.imp (.classMem A V) (synWb (.classMem A B) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  have p0000 := @gEleq2i B (.cab x ph) A hyp_elab2g_2
  have p0001 :=
    @gElabg ph ps x A V
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_elab2g_1
  have p0002 :=
    @gSyl5bb (.classMem A B) (.classMem A (.cab x ph)) (.classMem A V) ps p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elab2`. -/
@[expose]
noncomputable def gElab2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elab2_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_elab2_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_elab2_3 : Nominal.NPrf (.classEq B (.cab x ph))) :
    Nominal.NPrf (synWb (.classMem A B) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gElab2g ph ps x A B (synCvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_elab2_2 hyp_elab2_3
  have p0001 := Nominal.mp hyp_elab2_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elab3gf`. -/
@[expose]
noncomputable def gElab3gf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_elab3gf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_elab3gf_2 : Nominal.NPrf (synWnf x ps))
    (hyp_elab3gf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.imp ps (.classMem A B)) (synWb (.classMem A (.cab x ph)) ps)) :=
  by
  have p0000 := @gElabgf ph ps x A (.cab x ph) hyp_elab3gf_1 hyp_elab3gf_2 hyp_elab3gf_3
  have p0001 := @gIbi (.classMem A (.cab x ph)) ps p0000
  have p0002 := @gPm221 ps (.classMem A (.cab x ph))
  have p0003 := @gImpbid2 (.neg ps) (.classMem A (.cab x ph)) ps p0001 p0002
  have p0004 := @gElabgf ph ps x A B hyp_elab3gf_1 hyp_elab3gf_2 hyp_elab3gf_3
  have p0005 := @gJa ps (.classMem A B) (synWb (.classMem A (.cab x ph)) ps) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_elab3g`. -/
@[expose]
noncomputable def gElab3g (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elab3g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.imp ps (.classMem A B)) (synWb (.classMem A (.cab x ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0002 := @gElab3gf ph ps x A B p0000 p0001 hyp_elab3g_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elab3`. -/
@[expose]
noncomputable def gElab3 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_elab3_1 : Nominal.NPrf (.imp ps (.classMem A (synCvv))))
    (hyp_elab3_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.classMem A (.cab x ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gElab3g ph ps x A (synCvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_elab3_2
  have p0001 := Nominal.mp hyp_elab3_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elrabf`. -/
@[expose]
noncomputable def gElrabf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_elrabf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_elrabf_2 : Nominal.NPrf (synWnfc x B))
    (hyp_elrabf_3 : Nominal.NPrf (synWnf x ps))
    (hyp_elrabf_4 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.classMem A (synCrab x B ph)) (synWa (.classMem A B) ps)) :=
  by
  have p0000 := @gElex A (synCrab x B ph)
  have p0001 := @gElex A B
  have p0002 := @gAdantr (.classMem A B) (.classMem A (synCvv)) ps p0001
  have p0003 := (Nominal.classEqRefl (synCrab x B ph))
  have p0004 :=
    @gEleq2i (synCrab x B ph) (.cab x (synWa (.classMem (.cv x) B) ph)) A p0003
  have p0005 := @gNfel x A B hyp_elrabf_1 hyp_elrabf_2
  have p0006 := @gNfan (.classMem A B) ps x p0005 hyp_elrabf_3
  have p0007 := @gEleq1 (.cv x) A B
  have p0008 :=
    @gAnbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0007
      hyp_elrabf_4
  have p0009 :=
    @gElabgf (synWa (.classMem (.cv x) B) ph) (synWa (.classMem A B) ps) x A (synCvv)
      hyp_elrabf_1 p0006 p0008
  have p0010 :=
    @gSyl5bb (.classMem A (synCrab x B ph))
      (.classMem A (.cab x (synWa (.classMem (.cv x) B) ph))) (.classMem A (synCvv))
      (synWa (.classMem A B) ps) p0004 p0009
  have p0011 :=
    @gPm521nii (.classMem A (synCrab x B ph)) (.classMem A (synCvv))
      (synWa (.classMem A B) ps) p0000 p0002 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_elrab`. -/
@[expose]
noncomputable def gElrab (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elrab_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.classMem A (synCrab x B ph)) (synWa (.classMem A B) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfcv x B
      (by
        first
        | (aesop))
  have p0002 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0003 := @gElrabf ph ps x A B p0000 p0001 p0002 hyp_elrab_1
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elrab2`. -/
@[expose]
noncomputable def gElrab2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elrab2_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_elrab2_2 : Nominal.NPrf (.classEq C (synCrab x B ph))) :
    Nominal.NPrf (synWb (.classMem A C) (synWa (.classMem A B) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @gEleq2i C (synCrab x B ph) A hyp_elrab2_2
  have p0001 :=
    @gElrab ph ps x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_elrab2_1
  have p0002 :=
    @gBitri (.classMem A C) (.classMem A (synCrab x B ph)) (synWa (.classMem A B) ps)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ralab`. -/
@[expose]
noncomputable def gRalab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralab_1 : Nominal.NPrf (.imp (.objEq y x) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWral x (.cab y ph) ch) (.all x (.imp ps ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := (Nominal.biimpRefl (synWral x (.cab y ph) ch))
  have p0001 := @gVex x
  have p0002_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (synWb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_ralab_1
  have p0002 :=
    @gElab ph ps y (.cv x)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0001 p0002_e01_recanon
  have p0003 := @gImbi1i (.classMem (.cv x) (.cab y ph)) ps ch p0002
  have p0004 := @gAlbii (.imp (.classMem (.cv x) (.cab y ph)) ch) (.imp ps ch) x p0003
  have p0005 :=
    @gBitri (synWral x (.cab y ph) ch)
      (.all x (.imp (.classMem (.cv x) (.cab y ph)) ch)) (.all x (.imp ps ch)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_rexab`. -/
@[expose]
noncomputable def gRexab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralab_1 : Nominal.NPrf (.imp (.objEq y x) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWrex x (.cab y ph) ch) (synWex x (synWa ps ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := (Nominal.biimpRefl (synWrex x (.cab y ph) ch))
  have p0001 := @gVex x
  have p0002_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (synWb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_ralab_1
  have p0002 :=
    @gElab ph ps y (.cv x)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0001 p0002_e01_recanon
  have p0003 := @gAnbi1i (.classMem (.cv x) (.cab y ph)) ps ch p0002
  have p0004 :=
    @gExbii (synWa (.classMem (.cv x) (.cab y ph)) ch) (synWa ps ch) x p0003
  have p0005 :=
    @gBitri (synWrex x (.cab y ph) ch)
      (synWex x (synWa (.classMem (.cv x) (.cab y ph)) ch)) (synWex x (synWa ps ch))
      p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_rexrab`. -/
@[expose]
noncomputable def gRexrab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (dv_A_y : y ∉ A.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralab_1 : Nominal.NPrf (.imp (.objEq y x) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWrex x (synCrab y A ph) ch) (synWrex x A (synWa ps ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (synWb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_ralab_1
  have p0000 :=
    @gElrab ph ps y (.cv x) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000_e00_recanon
  have p0001 :=
    @gAnbi1i (.classMem (.cv x) (synCrab y A ph)) (synWa (.classMem (.cv x) A) ps) ch
      p0000
  have p0002 := @gAnass (.classMem (.cv x) A) ps ch
  have p0003 :=
    @gBitri (synWa (.classMem (.cv x) (synCrab y A ph)) ch)
      (synWa (synWa (.classMem (.cv x) A) ps) ch)
      (synWa (.classMem (.cv x) A) (synWa ps ch)) p0001 p0002
  have p0004 := @gRexbii2 ch (synWa ps ch) x (synCrab y A ph) A p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ralab2`. -/
@[expose]
noncomputable def gRalab2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralab2_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ps ch))) :
    Nominal.NPrf (synWb (synWral x (.cab y ph) ps) (.all y (.imp ph ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := (Nominal.biimpRefl (synWral x (.cab y ph) ps))
  have p0001 :=
    @gNfsab1 ph y x
      (by
        first
        | (aesop))
  have p0002 :=
    @gNfv ps y
      (by
        first
        | (aesop))
  have p0003 := @gNfim (.classMem (.cv x) (.cab y ph)) ps y p0001 p0002
  have p0004 :=
    @gNfv (.imp ph ch) x
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              Finset.mem_union] at ⊢;
            aesop))
  have p0005 := @gEleq1 (.cv x) (.cv y) (.cab y ph)
  have p0006 := @gAbid ph y
  have p0007 :=
    @gSyl6bb (.classEq (.cv x) (.cv y)) (.classMem (.cv x) (.cab y ph))
      (.classMem (.cv y) (.cab y ph)) ph p0005 p0006
  have p0008_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (synWb ps ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_ralab2_1
  have p0008 :=
    @gImbi12d (.classEq (.cv x) (.cv y)) (.classMem (.cv x) (.cab y ph)) ph ps ch p0007
      p0008_e01_recanon
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (.imp (.classMem (.cv x) (.cab y ph)) ps) (.imp ph ch))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gCbval (.imp (.classMem (.cv x) (.cab y ph)) ps) (.imp ph ch) x y p0003 p0004
      p0009_e02_recanon
  have p0010 :=
    @gBitri (synWral x (.cab y ph) ps)
      (.all x (.imp (.classMem (.cv x) (.cab y ph)) ps)) (.all y (.imp ph ch)) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_abidnf`. -/
@[expose]
noncomputable def gAbidnf (x : Var) (z : Var) (A : Class) (dv_A_z : z ∉ A.fv)
    (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (synWnfc x A) (.classEq (.cab z (.all x (.classMem (.cv z) A))) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv
  have p0000 := @gSp (.classMem (.cv z) A) x
  have p0001 :=
    @gNfcr x z A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 := @gNfrd (synWnfc x A) (.classMem (.cv z) A) x p0001
  have p0003 :=
    @gImpbid2 (synWnfc x A) (.all x (.classMem (.cv z) A)) (.classMem (.cv z) A) p0000
      p0002
  have p0004 :=
    @gEqabcdv (synWnfc x A) (.all x (.classMem (.cv z) A)) z A
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wnfc,
              Finset.mem_erase] at ⊢;
            aesop))
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eueq`. -/
@[expose]
noncomputable def gEueq (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (.classMem A (synCvv)) (synWeu x (.classEq (.cv x) A))) :=
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
  have p0000 := @gEqtr3 (.cv x) (.cv y) A
  have p0001 :=
    @gGen2
      (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) A)) (.classEq (.cv x) (.cv y)))
      x y p0000
  have p0002 :=
    @gBiantru
      (.all x (.all y (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) A))
            (.classEq (.cv x) (.cv y)))))
      (synWex x (.classEq (.cv x) A)) p0001
  have p0003 :=
    @gIsset x A
      (by
        first
        | (aesop))
  have p0004 := @gEqeq1 (.cv x) (.cv y) A
  have p0005_e00_recanon :
    Nominal.NPrf (.imp (.objEq x y) (synWb (.classEq (.cv x) A) (.classEq (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gEu4 (.classEq (.cv x) A) (.classEq (.cv y) A) x y
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
      p0005_e00_recanon
  have p0006_e02_recanon :
    Nominal.NPrf
      (synWb (synWeu x (.classEq (.cv x) A)) (synWa (synWex x (.classEq (.cv x) A)) (.all x
            (.all y (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) A))
                (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gN3bitr4i (synWex x (.classEq (.cv x) A))
      (synWa (synWex x (.classEq (.cv x) A)) (.all x (.all y
            (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) A))
              (.classEq (.cv x) (.cv y))))))
      (.classMem A (synCvv)) (synWeu x (.classEq (.cv x) A)) p0002 p0003
      p0006_e02_recanon
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_eueq1`. -/
@[expose]
noncomputable def gEueq1 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_eueq1_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWeu x (.classEq (.cv x) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gEueq x A
      (by
        first
        | (aesop))
  have p0001 :=
    @gMpbi (.classMem A (synCvv)) (synWeu x (.classEq (.cv x) A)) hyp_eueq1_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_moeq`. -/
@[expose]
noncomputable def gMoeq (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWmo x (.classEq (.cv x) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gIsset x A
      (by
        first
        | (aesop))
  have p0001 :=
    @gEueq x A
      (by
        first
        | (aesop))
  have p0002 :=
    @gBitr3i (synWex x (.classEq (.cv x) A)) (.classMem A (synCvv))
      (synWeu x (.classEq (.cv x) A)) p0000 p0001
  have p0003 :=
    @gBiimpi (synWex x (.classEq (.cv x) A)) (synWeu x (.classEq (.cv x) A)) p0002
  have p0004 := (Nominal.biimpRefl (synWmo x (.classEq (.cv x) A)))
  have p0005 :=
    @gMpbir (synWmo x (.classEq (.cv x) A))
      (.imp (synWex x (.classEq (.cv x) A)) (synWeu x (.classEq (.cv x) A))) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_rmo4`. -/
@[expose]
noncomputable def gRmo4 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_x_y : x ≠ y) (hyp_rmo4_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWrmo x A ph)
        (synWral x A (synWral y A (.imp (synWa ph ps) (.objEq x y))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.biimpRefl (synWrmo x A ph))
  have p0001 := @gAn4 (.classMem (.cv x) A) ph (.classMem (.cv y) A) ps
  have p0002 := @gAncom (.classMem (.cv x) A) (.classMem (.cv y) A)
  have p0003 :=
    @gAnbi1i (synWa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (synWa (.classMem (.cv y) A) (.classMem (.cv x) A)) (synWa ph ps) p0002
  have p0004 :=
    @gBitri (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) A) ps))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) A)) (synWa ph ps))
      (synWa (synWa (.classMem (.cv y) A) (.classMem (.cv x) A)) (synWa ph ps)) p0001
      p0003
  have p0005 :=
    @gImbi1i (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) A) ps))
      (synWa (synWa (.classMem (.cv y) A) (.classMem (.cv x) A)) (synWa ph ps))
      (.objEq x y) p0004
  have p0006 :=
    @gImpexp (synWa (.classMem (.cv y) A) (.classMem (.cv x) A)) (synWa ph ps)
      (.objEq x y)
  have p0007 :=
    @gImpexp (.classMem (.cv y) A) (.classMem (.cv x) A)
      (.imp (synWa ph ps) (.objEq x y))
  have p0008 :=
    @gN3bitri
      (.imp (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) A) ps))
        (.objEq x y))
      (.imp (synWa (synWa (.classMem (.cv y) A) (.classMem (.cv x) A)) (synWa ph ps))
        (.objEq x y))
      (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv x) A))
        (.imp (synWa ph ps) (.objEq x y)))
      (.imp (.classMem (.cv y) A)
        (.imp (.classMem (.cv x) A) (.imp (synWa ph ps) (.objEq x y))))
      p0005 p0006 p0007
  have p0009 :=
    @gAlbii
      (.imp (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) A) ps))
        (.objEq x y))
      (.imp (.classMem (.cv y) A)
        (.imp (.classMem (.cv x) A) (.imp (synWa ph ps) (.objEq x y))))
      y p0008
  have p0010 :=
    (Nominal.biimpRefl
      (synWral y A (.imp (.classMem (.cv x) A) (.imp (synWa ph ps) (.objEq x y)))))
  have p0011 :=
    @gR1921v (.classMem (.cv x) A) (.imp (synWa ph ps) (.objEq x y)) y A
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
  have p0012 :=
    @gN3bitr2i
      (.all y (.imp (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) A) ps))
          (.objEq x y)))
      (.all y (.imp (.classMem (.cv y) A)
          (.imp (.classMem (.cv x) A) (.imp (synWa ph ps) (.objEq x y)))))
      (synWral y A (.imp (.classMem (.cv x) A) (.imp (synWa ph ps) (.objEq x y))))
      (.imp (.classMem (.cv x) A) (synWral y A (.imp (synWa ph ps) (.objEq x y)))) p0009
      p0010 p0011
  have p0013 :=
    @gAlbii
      (.all y (.imp (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) A) ps))
          (.objEq x y)))
      (.imp (.classMem (.cv x) A) (synWral y A (.imp (synWa ph ps) (.objEq x y)))) x
      p0012
  have p0014 := @gEleq1 (.cv x) (.cv y) A
  have p0015_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (.classMem (.cv x) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0015 :=
    @gAnbi12d (.objEq x y) (.classMem (.cv x) A) (.classMem (.cv y) A) ph ps
      p0015_e00_recanon hyp_rmo4_1
  have p0016 :=
    @gMo4 (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) A) ps) x y
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
      (by
        first
        | (aesop))
      p0015
  have p0017 :=
    (Nominal.biimpRefl (synWral x A (synWral y A (.imp (synWa ph ps) (.objEq x y)))))
  have p0018 :=
    @gN3bitr4i
      (.all x (.all y (.imp
            (synWa (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv y) A) ps))
            (.objEq x y))))
      (.all x (.imp (.classMem (.cv x) A) (synWral y A (.imp (synWa ph ps) (.objEq x y)))))
      (synWmo x (synWa (.classMem (.cv x) A) ph))
      (synWral x A (synWral y A (.imp (synWa ph ps) (.objEq x y)))) p0013 p0016 p0017
  have p0019 :=
    @gBitri (synWrmo x A ph) (synWmo x (synWa (.classMem (.cv x) A) ph))
      (synWral x A (synWral y A (.imp (synWa ph ps) (.objEq x y)))) p0000 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_reu4`. -/
@[expose]
noncomputable def gReu4 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_x_y : x ≠ y) (hyp_rmo4_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWreu x A ph) (synWa (synWrex x A ph)
          (synWral x A (synWral y A (.imp (synWa ph ps) (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 := @gReu5 ph x A
  have p0001 :=
    @gRmo4 ph ps x y A
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
      hyp_rmo4_1
  have p0002 :=
    @gAnbi2i (synWrmo x A ph)
      (synWral x A (synWral y A (.imp (synWa ph ps) (.objEq x y)))) (synWrex x A ph)
      p0001
  have p0003 :=
    @gBitri (synWreu x A ph) (synWa (synWrex x A ph) (synWrmo x A ph))
      (synWa (synWrex x A ph)
        (synWral x A (synWral y A (.imp (synWa ph ps) (.objEq x y)))))
      p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_dfsbcq`. -/
@[expose]
noncomputable def gDfsbcq (ph : Wff) (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWsbc A x ph) (synWsbc B x ph))) :=
  by
  have p0000 := @gEleq1 A B (.cab x ph)
  have p0001 := (Nominal.biimpRefl (synWsbc A x ph))
  have p0002 := (Nominal.biimpRefl (synWsbc B x ph))
  have p0003 :=
    @gN3bitr4g (.classEq A B) (.classMem A (.cab x ph)) (.classMem B (.cab x ph))
      (synWsbc A x ph) (synWsbc B x ph) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_dfsbcq2`. -/
@[expose]
noncomputable def gDfsbcq2 (ph : Wff) (x : Var) (y : Var) (A : Class) :
    Nominal.NPrf
      (.imp (.classEq (.cv y) A) (synWb (synWsb y x ph) (synWsbc A x ph))) :=
  by
  have p0000 := @gEleq1 (.cv y) A (.cab x ph)
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0002 := (Nominal.biimpRefl (synWsbc A x ph))
  have p0003 := @gBicomi (synWsbc A x ph) (.classMem A (.cab x ph)) p0002
  have p0004 :=
    @gN3bitr3g (.classEq (.cv y) A) (.classMem (.cv y) (.cab x ph))
      (.classMem A (.cab x ph)) (synWsb y x ph) (synWsbc A x ph) p0000 p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sbsbc`. -/
@[expose]
noncomputable def gSbsbc (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWb (synWsb y x ph) (synWsbc (.cv y) x ph)) :=
  by
  have p0000 := @gEqid (.cv y)
  have p0001 := @gDfsbcq2 ph x y (.cv y)
  have p0002_e00_recanon : Nominal.NPrf (.objEq y y) :=
    Nominal.RecanonTransportDev.transport
      (by exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _) p0000
  have p0002_e01_recanon :
    Nominal.NPrf (.imp (.objEq y y) (synWb (synWsb y x ph) (synWsbc (.cv y) x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex synWsbc
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 := Nominal.mp p0002_e00_recanon p0002_e01_recanon
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbcex`. -/
@[expose]
noncomputable def gSbcex (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (synWsbc A x ph) (.classMem A (synCvv))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWsbc A x ph))
  have p0001 := @gElex A (.cab x ph)
  have p0002 :=
    @gSylbi (synWsbc A x ph) (.classMem A (.cab x ph)) (.classMem A (synCvv)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_spsbc`. -/
@[expose]
noncomputable def gSpsbc (ph : Wff) (x : Var) (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.imp (.all x ph) (synWsbc A x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
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
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gStdpc4 ph x y
  have p0001 := @gSbsbc ph x y
  have p0002 := @gSylib (.all x ph) (synWsb y x ph) (synWsbc (.cv y) x ph) p0000 p0001
  have p0003 := @gDfsbcq ph x (.cv y) A
  have p0004 :=
    @gSyl5ib (.all x ph) (synWsbc (.cv y) x ph) (.classEq (.cv y) A) (synWsbc A x ph)
      p0002 p0003
  have p0005 :=
    @gVtocleg (.imp (.all x ph) (synWsbc A x ph)) y A V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfsbc1d`. -/
@[expose]
noncomputable def gNfsbc1d (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_nfsbc1d_2 : Nominal.NPrf (.imp ph (synWnfc x A))) :
    Nominal.NPrf (.imp ph (synWnf x (synWsbc A x ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWsbc A x ps))
  have p0001 := @gNfab1 ps x
  have p0002 := @gA1i (synWnfc x (.cab x ps)) ph p0001
  have p0003 := @gNfeld ph x A (.cab x ps) hyp_nfsbc1d_2 p0002
  have p0004 := @gNfxfrd (synWsbc A x ps) (.classMem A (.cab x ps)) ph x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfsbcd`. -/
@[expose]
noncomputable def gNfsbcd (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_nfsbcd_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfsbcd_2 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_nfsbcd_3 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (synWsbc A y ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWsbc A y ps))
  have p0001 := @gNfabd ph ps x y hyp_nfsbcd_1 hyp_nfsbcd_3
  have p0002 := @gNfeld ph x A (.cab y ps) hyp_nfsbcd_2 p0001
  have p0003 := @gNfxfrd (synWsbc A y ps) (.classMem A (.cab y ps)) ph x p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sbcco`. -/
@[expose]
noncomputable def gSbcco (ph : Wff) (x : Var) (y : Var) (A : Class)
    (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf (synWb (synWsbc A y (synWsbc (.cv y) x ph)) (synWsbc A x ph)) :=
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
  have p0000 := @gSbcex (synWsbc (.cv y) x ph) y A
  have p0001 := @gSbcex ph x A
  have p0002 := @gDfsbcq (synWsbc (.cv y) x ph) y (.cv z) A
  have p0003 := @gDfsbcq ph x (.cv z) A
  have p0004 := @gSbsbc ph x y
  have p0005 := @gSbbii (synWsb y x ph) (synWsbc (.cv y) x ph) y z p0004
  have p0006 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0007 := @gSbco2 ph x z y p0006
  have p0008 := @gSbsbc (synWsbc (.cv y) x ph) y z
  have p0009 :=
    @gN3bitr3ri (synWsb z y (synWsb y x ph)) (synWsb z y (synWsbc (.cv y) x ph))
      (synWsb z x ph) (synWsbc (.cv z) y (synWsbc (.cv y) x ph)) p0005 p0007 p0008
  have p0010 := @gSbsbc ph x z
  have p0011 :=
    @gBitri (synWsbc (.cv z) y (synWsbc (.cv y) x ph)) (synWsb z x ph)
      (synWsbc (.cv z) x ph) p0009 p0010
  have p0012 :=
    @gVtoclbg (synWsbc (.cv z) y (synWsbc (.cv y) x ph)) (synWsbc (.cv z) x ph)
      (synWsbc A y (synWsbc (.cv y) x ph)) (synWsbc A x ph) z A (synCvv)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      p0002 p0003 p0011
  have p0013 :=
    @gPm521nii (synWsbc A y (synWsbc (.cv y) x ph)) (.classMem A (synCvv))
      (synWsbc A x ph) p0000 p0001 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_sbc5`. -/
@[expose]
noncomputable def gSbc5 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (synWsbc A x ph) (synWex x (synWa (.classEq (.cv x) A) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gSbcex ph x A
  have p0001 := @gExsimpl (.classEq (.cv x) A) ph x
  have p0002 :=
    @gIsset x A
      (by
        first
        | (aesop))
  have p0003 :=
    @gSylibr (synWex x (synWa (.classEq (.cv x) A) ph))
      (synWex x (.classEq (.cv x) A)) (.classMem A (synCvv)) p0001 p0002
  have p0004 := @gDfsbcq2 ph x y A
  have p0005 := @gEqeq2 (.cv y) A (.cv x)
  have p0006_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) A) (synWb (.objEq x y) (.classEq (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0005
  have p0006 :=
    @gAnbi1d (.classEq (.cv y) A) (.objEq x y) (.classEq (.cv x) A) ph p0006_e00_recanon
  have p0007 :=
    @gExbidv (.classEq (.cv y) A) (synWa (.objEq x y) ph)
      (synWa (.classEq (.cv x) A) ph) x
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
      p0006
  have p0008 :=
    @gSb5 ph x y
      (by
        first
        | (aesop))
  have p0009 :=
    @gVtoclbg (synWsb y x ph) (synWex x (synWa (.objEq x y) ph)) (synWsbc A x ph)
      (synWex x (synWa (.classEq (.cv x) A) ph)) y A (synCvv)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      p0004 p0007 p0008
  have p0010 :=
    @gPm521nii (synWsbc A x ph) (.classMem A (synCvv))
      (synWex x (synWa (.classEq (.cv x) A) ph)) p0000 p0003 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_sbc6g`. -/
@[expose]
noncomputable def gSbc6g (ph : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem A V)
        (synWb (synWsbc A x ph) (.all x (.imp (.classEq (.cv x) A) ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := @gNfe1 (synWa (.classEq (.cv x) A) ph) x
  have p0001 :=
    @gCeqex ph x A
      (by
        first
        | (aesop))
  have p0002 :=
    @gCeqsalg ph (synWex x (synWa (.classEq (.cv x) A) ph)) x A V
      (by
        first
        | (aesop))
      p0000 p0001
  have p0003 :=
    @gSbc5 ph x A
      (by
        first
        | (aesop))
  have p0004 :=
    @gSyl6rbbr (.classMem A V) (.all x (.imp (.classEq (.cv x) A) ph))
      (synWex x (synWa (.classEq (.cv x) A) ph)) (synWsbc A x ph) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sbciegft`. -/
@[expose]
noncomputable def gSbciegft (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (synWnf x ps)
          (.all x (.imp (.classEq (.cv x) A) (synWb ph ps)))) (synWb (synWsbc A x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @gSbc5 ph x A
      (by
        first
        | (aesop))
  have p0001 := @gBi1 ph ps
  have p0002 := @gImim2i (synWb ph ps) (.imp ph ps) (.classEq (.cv x) A) p0001
  have p0003 :=
    @gImp3a (.imp (.classEq (.cv x) A) (synWb ph ps)) (.classEq (.cv x) A) ph ps p0002
  have p0004 :=
    @gAlimi (.imp (.classEq (.cv x) A) (synWb ph ps))
      (.imp (synWa (.classEq (.cv x) A) ph) ps) x p0003
  have p0005 := @gN1923t (synWa (.classEq (.cv x) A) ph) ps x
  have p0006 :=
    @gBiimpa (synWnf x ps) (.all x (.imp (synWa (.classEq (.cv x) A) ph) ps))
      (.imp (synWex x (synWa (.classEq (.cv x) A) ph)) ps) p0005
  have p0007 :=
    @gSylan2 (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (synWnf x ps)
      (.all x (.imp (synWa (.classEq (.cv x) A) ph) ps))
      (.imp (synWex x (synWa (.classEq (.cv x) A) ph)) ps) p0004 p0006
  have p0008 :=
    @gN3adant1 (synWnf x ps) (.all x (.imp (.classEq (.cv x) A) (synWb ph ps)))
      (.imp (synWex x (synWa (.classEq (.cv x) A) ph)) ps) (.classMem A V) p0007
  have p0009 :=
    @gSyl5bi (synWsbc A x ph) (synWex x (synWa (.classEq (.cv x) A) ph))
      (synW3a (.classMem A V) (synWnf x ps)
        (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))))
      ps p0000 p0008
  have p0010 := @gBi2 ph ps
  have p0011 := @gImim2i (synWb ph ps) (.imp ps ph) (.classEq (.cv x) A) p0010
  have p0012 :=
    @gCom23 (.imp (.classEq (.cv x) A) (synWb ph ps)) (.classEq (.cv x) A) ps ph p0011
  have p0013 :=
    @gAlimi (.imp (.classEq (.cv x) A) (synWb ph ps))
      (.imp ps (.imp (.classEq (.cv x) A) ph)) x p0012
  have p0014 := @gN1921t ps (.imp (.classEq (.cv x) A) ph) x
  have p0015 :=
    @gBiimpa (synWnf x ps) (.all x (.imp ps (.imp (.classEq (.cv x) A) ph)))
      (.imp ps (.all x (.imp (.classEq (.cv x) A) ph))) p0014
  have p0016 :=
    @gSylan2 (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (synWnf x ps)
      (.all x (.imp ps (.imp (.classEq (.cv x) A) ph)))
      (.imp ps (.all x (.imp (.classEq (.cv x) A) ph))) p0013 p0015
  have p0017 :=
    @gN3adant1 (synWnf x ps) (.all x (.imp (.classEq (.cv x) A) (synWb ph ps)))
      (.imp ps (.all x (.imp (.classEq (.cv x) A) ph))) (.classMem A V) p0016
  have p0018 :=
    @gSbc6g ph x A V
      (by
        first
        | (aesop))
  have p0019 :=
    @gN3ad2ant1 (.classMem A V) (synWnf x ps)
      (synWb (synWsbc A x ph) (.all x (.imp (.classEq (.cv x) A) ph)))
      (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) p0018
  have p0020 :=
    @gSylibrd
      (synW3a (.classMem A V) (synWnf x ps)
        (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))))
      ps (.all x (.imp (.classEq (.cv x) A) ph)) (synWsbc A x ph) p0017 p0019
  have p0021 :=
    @gImpbid
      (synW3a (.classMem A V) (synWnf x ps)
        (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))))
      (synWsbc A x ph) ps p0009 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_sbciegf`. -/
@[expose]
noncomputable def gSbciegf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (hyp_sbciegf_1 : Nominal.NPrf (synWnf x ps))
    (hyp_sbciegf_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (synWb (synWsbc A x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := Nominal.gen hyp_sbciegf_2 x
  have p0001 :=
    @gSbciegft ph ps x A V
      (by
        first
        | (aesop))
  have p0002 :=
    @gMp3an23 (.classMem A V) (synWnf x ps)
      (.all x (.imp (.classEq (.cv x) A) (synWb ph ps))) (synWb (synWsbc A x ph) ps)
      hyp_sbciegf_1 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbcieg`. -/
@[expose]
noncomputable def gSbcieg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_sbcieg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (synWb (synWsbc A x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := @gElex A V
  have p0001 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0002 :=
    @gSbciegf ph ps x A (synCvv)
      (by
        first
        | (aesop))
      p0001 hyp_sbcieg_1
  have p0003 :=
    @gSyl (.classMem A V) (.classMem A (synCvv)) (synWb (synWsbc A x ph) ps) p0000
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sbciedf`. -/
@[expose]
noncomputable def gSbciedf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (V : Class) (dv_A_x : x ∉ A.fv)
    (hyp_sbcied_1 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_sbcied_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (synWb ps ch)))
    (hyp_sbciedf_3 : Nominal.NPrf (synWnf x ph))
    (hyp_sbciedf_4 : Nominal.NPrf (.imp ph (synWnf x ch))) :
    Nominal.NPrf (.imp ph (synWb (synWsbc A x ps) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := @gEx ph (.classEq (.cv x) A) (synWb ps ch) hyp_sbcied_2
  have p0001 :=
    @gAlrimi ph (.imp (.classEq (.cv x) A) (synWb ps ch)) x hyp_sbciedf_3 p0000
  have p0002 :=
    @gSbciegft ps ch x A V
      (by
        first
        | (aesop))
  have p0003 :=
    @gSyl3anc ph (.classMem A V) (synWnf x ch)
      (.all x (.imp (.classEq (.cv x) A) (synWb ps ch))) (synWb (synWsbc A x ps) ch)
      hyp_sbcied_1 hyp_sbciedf_4 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eqsbc1`. -/
@[expose]
noncomputable def gEqsbc1 (x : Var) (A : Class) (B : Class) (V : Class)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (synWsbc A x (.classEq (.cv x) B)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gDfsbcq (.classEq (.cv x) B) x (.cv y) A
  have p0001 := @gEqeq1 (.cv y) A B
  have p0002 := @gSbsbc (.classEq (.cv x) B) x y
  have p0003 :=
    @gEqsb1 x y B
      (by
        first
        | (aesop))
  have p0004 :=
    @gBitr3i (synWsbc (.cv y) x (.classEq (.cv x) B)) (synWsb y x (.classEq (.cv x) B))
      (.classEq (.cv y) B) p0002 p0003
  have p0005 :=
    @gVtoclbg (synWsbc (.cv y) x (.classEq (.cv x) B)) (.classEq (.cv y) B)
      (synWsbc A x (.classEq (.cv x) B)) (.classEq A B) y A V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_sbcimg`. -/
@[expose]
noncomputable def gSbcimg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (synWsbc A x (.imp ph ps))
          (.imp (synWsbc A x ph) (synWsbc A x ps)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
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
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gDfsbcq2 (.imp ph ps) x y A
  have p0001 := @gDfsbcq2 ph x y A
  have p0002 := @gDfsbcq2 ps x y A
  have p0003 :=
    @gImbi12d (.classEq (.cv y) A) (synWsb y x ph) (synWsbc A x ph) (synWsb y x ps)
      (synWsbc A x ps) p0001 p0002
  have p0004 := @gSbim ph ps x y
  have p0005 :=
    @gVtoclbg (synWsb y x (.imp ph ps)) (.imp (synWsb y x ph) (synWsb y x ps))
      (synWsbc A x (.imp ph ps)) (.imp (synWsbc A x ph) (synWsbc A x ps)) y A V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
              NFChoice.Compiler.CoreFVSimp.fv_wff_imp, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0000 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_sbcan`. -/
@[expose]
noncomputable def gSbcan (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWsbc A x (synWa ph ps)) (synWa (synWsbc A x ph) (synWsbc A x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
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
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gSbcex (synWa ph ps) x A
  have p0001 := @gSbcex ps x A
  have p0002 :=
    @gAdantl (synWsbc A x ps) (.classMem A (synCvv)) (synWsbc A x ph) p0001
  have p0003 := @gDfsbcq2 (synWa ph ps) x y A
  have p0004 := @gDfsbcq2 ph x y A
  have p0005 := @gDfsbcq2 ps x y A
  have p0006 :=
    @gAnbi12d (.classEq (.cv y) A) (synWsb y x ph) (synWsbc A x ph) (synWsb y x ps)
      (synWsbc A x ps) p0004 p0005
  have p0007 := @gSban ph ps x y
  have p0008 :=
    @gVtoclbg (synWsb y x (synWa ph ps)) (synWa (synWsb y x ph) (synWsb y x ps))
      (synWsbc A x (synWa ph ps)) (synWa (synWsbc A x ph) (synWsbc A x ps)) y A
      (synCvv)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0003 p0006 p0007
  have p0009 :=
    @gPm521nii (synWsbc A x (synWa ph ps)) (.classMem A (synCvv))
      (synWa (synWsbc A x ph) (synWsbc A x ps)) p0000 p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_sbceqal`. -/
@[expose]
noncomputable def gSbceqal (x : Var) (A : Class) (B : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (.imp (.all x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)))
          (.classEq A B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  have p0000 := @gSpsbc (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)) x A V
  have p0001 := @gSbcimg (.classEq (.cv x) A) (.classEq (.cv x) B) x A V
  have p0002 := @gEqid A
  have p0003 :=
    @gEqsbc1 x A A V
      (by
        first
        | (aesop))
  have p0004 :=
    @gMpbiri (.classMem A V) (synWsbc A x (.classEq (.cv x) A)) (.classEq A A) p0002
      p0003
  have p0005 :=
    @gPm55 (synWsbc A x (.classEq (.cv x) A)) (synWsbc A x (.classEq (.cv x) B))
  have p0006 :=
    @gSyl (.classMem A V) (synWsbc A x (.classEq (.cv x) A))
      (synWb (.imp (synWsbc A x (.classEq (.cv x) A)) (synWsbc A x (.classEq (.cv x) B)))
        (synWsbc A x (.classEq (.cv x) B)))
      p0004 p0005
  have p0007 :=
    @gEqsbc1 x A B V
      (by
        first
        | (aesop))
  have p0008 :=
    @gN3bitrd (.classMem A V)
      (synWsbc A x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)))
      (.imp (synWsbc A x (.classEq (.cv x) A)) (synWsbc A x (.classEq (.cv x) B)))
      (synWsbc A x (.classEq (.cv x) B)) (.classEq A B) p0001 p0006 p0007
  have p0009 :=
    @gSylibd (.classMem A V) (.all x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)))
      (synWsbc A x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B))) (.classEq A B) p0000
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_sbeqalb`. -/
@[expose]
noncomputable def gSbeqalb (ph : Wff) (x : Var) (A : Class) (B : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (.imp (synWa (.all x (synWb ph (.classEq (.cv x) A)))
            (.all x (synWb ph (.classEq (.cv x) B)))) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  have p0000 := @gBibi1 ph (.classEq (.cv x) A) (.classEq (.cv x) B)
  have p0001 :=
    @gBiimpa (synWb ph (.classEq (.cv x) A)) (synWb ph (.classEq (.cv x) B))
      (synWb (.classEq (.cv x) A) (.classEq (.cv x) B)) p0000
  have p0002 :=
    @gBiimpd (synWa (synWb ph (.classEq (.cv x) A)) (synWb ph (.classEq (.cv x) B)))
      (.classEq (.cv x) A) (.classEq (.cv x) B) p0001
  have p0003 :=
    @gAlanimi (synWb ph (.classEq (.cv x) A)) (synWb ph (.classEq (.cv x) B))
      (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)) x p0002
  have p0004 :=
    @gSbceqal x A B V
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gSyl5
      (synWa (.all x (synWb ph (.classEq (.cv x) A)))
        (.all x (synWb ph (.classEq (.cv x) B))))
      (.all x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B))) (.classMem A V)
      (.classEq A B) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_sbcbid`. -/
@[expose]
noncomputable def gSbcbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_sbcbid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_sbcbid_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWsbc A x ps) (synWsbc A x ch))) :=
  by
  have p0000 := @gAbbid ph ps ch x hyp_sbcbid_1 hyp_sbcbid_2
  have p0001 := @gEleq2d ph (.cab x ps) (.cab x ch) A p0000
  have p0002 := (Nominal.biimpRefl (synWsbc A x ps))
  have p0003 := (Nominal.biimpRefl (synWsbc A x ch))
  have p0004 :=
    @gN3bitr4g ph (.classMem A (.cab x ps)) (.classMem A (.cab x ch)) (synWsbc A x ps)
      (synWsbc A x ch) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sbcbidv`. -/
@[expose]
noncomputable def gSbcbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_sbcbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWsbc A x ps) (synWsbc A x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gSbcbid ph ps ch x A p0000 hyp_sbcbidv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sbcbii`. -/
@[expose]
noncomputable def gSbcbii (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_sbcbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWsbc A x ph) (synWsbc A x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @gA1i (synWb ph ps) synWtru hyp_sbcbii_1
  have p0001 :=
    @gSbcbidv synWtru ph ps x A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @gTrud (synWb (synWsbc A x ph) (synWsbc A x ps)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbccomlem`. -/
@[expose]
noncomputable def gSbccomlem (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWsbc A x (synWsbc B y ph)) (synWsbc B y (synWsbc A x ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gExcom (synWa (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph)) x y
  have p0001 :=
    @gExdistr (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph) x y
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
  have p0002 := @gAn12 (.classEq (.cv x) A) (.classEq (.cv y) B) ph
  have p0003 :=
    @gExbii (synWa (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph))
      (synWa (.classEq (.cv y) B) (synWa (.classEq (.cv x) A) ph)) x p0002
  have p0004 :=
    @gN1942v (.classEq (.cv y) B) (synWa (.classEq (.cv x) A) ph) x
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
  have p0005 :=
    @gBitri (synWex x (synWa (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph)))
      (synWex x (synWa (.classEq (.cv y) B) (synWa (.classEq (.cv x) A) ph)))
      (synWa (.classEq (.cv y) B) (synWex x (synWa (.classEq (.cv x) A) ph))) p0003
      p0004
  have p0006 :=
    @gExbii (synWex x (synWa (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph)))
      (synWa (.classEq (.cv y) B) (synWex x (synWa (.classEq (.cv x) A) ph))) y p0005
  have p0007 :=
    @gN3bitr3i
      (synWex x (synWex y (synWa (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph))))
      (synWex y (synWex x (synWa (.classEq (.cv x) A) (synWa (.classEq (.cv y) B) ph))))
      (synWex x (synWa (.classEq (.cv x) A) (synWex y (synWa (.classEq (.cv y) B) ph))))
      (synWex y (synWa (.classEq (.cv y) B) (synWex x (synWa (.classEq (.cv x) A) ph))))
      p0000 p0001 p0006
  have p0008 :=
    @gSbc5 (synWex y (synWa (.classEq (.cv y) B) ph)) x A
      (by
        first
        | (aesop))
  have p0009 :=
    @gSbc5 (synWex x (synWa (.classEq (.cv x) A) ph)) y B
      (by
        first
        | (aesop))
  have p0010 :=
    @gN3bitr4i
      (synWex x (synWa (.classEq (.cv x) A) (synWex y (synWa (.classEq (.cv y) B) ph))))
      (synWex y (synWa (.classEq (.cv y) B) (synWex x (synWa (.classEq (.cv x) A) ph))))
      (synWsbc A x (synWex y (synWa (.classEq (.cv y) B) ph)))
      (synWsbc B y (synWex x (synWa (.classEq (.cv x) A) ph))) p0007 p0008 p0009
  have p0011 :=
    @gSbc5 ph y B
      (by
        first
        | (aesop))
  have p0012 :=
    @gSbcbii (synWsbc B y ph) (synWex y (synWa (.classEq (.cv y) B) ph)) x A p0011
  have p0013 :=
    @gSbc5 ph x A
      (by
        first
        | (aesop))
  have p0014 :=
    @gSbcbii (synWsbc A x ph) (synWex x (synWa (.classEq (.cv x) A) ph)) y B p0013
  have p0015 :=
    @gN3bitr4i (synWsbc A x (synWex y (synWa (.classEq (.cv y) B) ph)))
      (synWsbc B y (synWex x (synWa (.classEq (.cv x) A) ph)))
      (synWsbc A x (synWsbc B y ph)) (synWsbc B y (synWsbc A x ph)) p0010 p0012 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_sbccom`. -/
@[expose]
noncomputable def gSbccom (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWsbc A x (synWsbc B y ph)) (synWsbc B y (synWsbc A x ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let w : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w_ne_z : w ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have p0000 :=
    @gSbccomlem (synWsbc (.cv w) y (synWsbc (.cv z) x ph)) z w A B fresh_z_not_A
      fresh_w_not_A fresh_z_not_B fresh_w_not_B fresh_z_ne_w
  have p0001 :=
    @gSbccomlem ph y x (.cv w) (.cv z) (not_mem_class_variable _ _ fresh_y_ne_w)
      (not_mem_class_variable _ _ fresh_x_ne_w) (not_mem_class_variable _ _ fresh_y_ne_z)
      (not_mem_class_variable _ _ fresh_x_ne_z) (Ne.symm dv_x_y)
  have p0002 :=
    @gSbcbii (synWsbc (.cv w) y (synWsbc (.cv z) x ph))
      (synWsbc (.cv z) x (synWsbc (.cv w) y ph)) w B p0001
  have p0003 :=
    @gSbccomlem (synWsbc (.cv w) y ph) w x B (.cv z) fresh_w_not_B dv_B_x
      (not_mem_class_variable _ _ fresh_w_ne_z) (not_mem_class_variable _ _ fresh_x_ne_z)
      fresh_w_ne_x
  have p0004 :=
    @gBitri (synWsbc B w (synWsbc (.cv w) y (synWsbc (.cv z) x ph)))
      (synWsbc B w (synWsbc (.cv z) x (synWsbc (.cv w) y ph)))
      (synWsbc (.cv z) x (synWsbc B w (synWsbc (.cv w) y ph))) p0002 p0003
  have p0005 :=
    @gSbcbii (synWsbc B w (synWsbc (.cv w) y (synWsbc (.cv z) x ph)))
      (synWsbc (.cv z) x (synWsbc B w (synWsbc (.cv w) y ph))) z A p0004
  have p0006 :=
    @gSbccomlem (synWsbc (.cv z) x ph) z y A (.cv w) fresh_z_not_A dv_A_y
      (not_mem_class_variable _ _ fresh_z_ne_w) (not_mem_class_variable _ _ fresh_y_ne_w)
      fresh_z_ne_y
  have p0007 :=
    @gSbcbii (synWsbc A z (synWsbc (.cv w) y (synWsbc (.cv z) x ph)))
      (synWsbc (.cv w) y (synWsbc A z (synWsbc (.cv z) x ph))) w B p0006
  have p0008 :=
    @gN3bitr3i
      (synWsbc A z (synWsbc B w (synWsbc (.cv w) y (synWsbc (.cv z) x ph))))
      (synWsbc B w (synWsbc A z (synWsbc (.cv w) y (synWsbc (.cv z) x ph))))
      (synWsbc A z (synWsbc (.cv z) x (synWsbc B w (synWsbc (.cv w) y ph))))
      (synWsbc B w (synWsbc (.cv w) y (synWsbc A z (synWsbc (.cv z) x ph)))) p0000
      p0005 p0007
  have p0009 :=
    @gSbcco (synWsbc B w (synWsbc (.cv w) y ph)) x z A
      (not_mem_syn_wsbc z B w _ fresh_z_not_B
        (not_mem_syn_wsbc z (.cv w) y ph (not_mem_class_variable _ _ fresh_z_ne_w)
          fresh_z_not_ph))
  have p0010 :=
    @gSbcco (synWsbc A z (synWsbc (.cv z) x ph)) y w B
      (not_mem_syn_wsbc w A z _ fresh_w_not_A
        (not_mem_syn_wsbc w (.cv z) x ph (not_mem_class_variable _ _ fresh_w_ne_z)
          fresh_w_not_ph))
  have p0011 :=
    @gN3bitr3i
      (synWsbc A z (synWsbc (.cv z) x (synWsbc B w (synWsbc (.cv w) y ph))))
      (synWsbc B w (synWsbc (.cv w) y (synWsbc A z (synWsbc (.cv z) x ph))))
      (synWsbc A x (synWsbc B w (synWsbc (.cv w) y ph)))
      (synWsbc B y (synWsbc A z (synWsbc (.cv z) x ph))) p0008 p0009 p0010
  have p0012 := @gSbcco ph y w B fresh_w_not_ph
  have p0013 :=
    @gSbcbii (synWsbc B w (synWsbc (.cv w) y ph)) (synWsbc B y ph) x A p0012
  have p0014 := @gSbcco ph x z A fresh_z_not_ph
  have p0015 :=
    @gSbcbii (synWsbc A z (synWsbc (.cv z) x ph)) (synWsbc A x ph) y B p0014
  have p0016 :=
    @gN3bitr3i (synWsbc A x (synWsbc B w (synWsbc (.cv w) y ph)))
      (synWsbc B y (synWsbc A z (synWsbc (.cv z) x ph)))
      (synWsbc A x (synWsbc B y ph)) (synWsbc B y (synWsbc A x ph)) p0011 p0013 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_rspesbca`. -/
@[expose]
noncomputable def gRspesbca (ph : Wff) (x : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (synWa (.classMem A B) (synWsbc A x ph)) (synWrex x B ph)) :=
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
  have p0000 := @gDfsbcq2 ph x y A
  have p0001 :=
    @gRspcev (synWsb y x ph) (synWsbc A x ph) y A B
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
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      p0000
  have p0002 :=
    @gCbvrexsv ph x y B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @gSylibr (synWa (.classMem A B) (synWsbc A x ph)) (synWrex y B (synWsb y x ph))
      (synWrex x B ph) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_spesbc`. -/
@[expose]
noncomputable def gSpesbc (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (synWsbc A x ph) (synWex x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @gSbcex ph x A
  have p0001 :=
    @gRspesbca ph x A (synCvv)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
  have p0002 :=
    @gMpancom (.classMem A (synCvv)) (synWsbc A x ph) (synWrex x (synCvv) ph) p0000
      p0001
  have p0003 := @gRexv ph x
  have p0004 :=
    @gSylib (synWsbc A x ph) (synWrex x (synCvv) ph) (synWex x ph) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_csbeq1`. -/
@[expose]
noncomputable def gCsbeq1 (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCsb A x C) (synCsb B x C))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gDfsbcq (.classMem (.cv y) C) x A B
  have p0001 :=
    @gAbbidv (.classEq A B) (synWsbc A x (.classMem (.cv y) C))
      (synWsbc B x (.classMem (.cv y) C)) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCsb x y A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCsb x y B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (.cab y (synWsbc A x (.classMem (.cv y) C)))
      (.cab y (synWsbc B x (.classMem (.cv y) C))) (synCsb A x C) (synCsb B x C) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_csbeq1d`. -/
@[expose]
noncomputable def gCsbeq1d (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (hyp_csbeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCsb A x C) (synCsb B x C))) :=
  by
  have p0000 := @gCsbeq1 x A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCsb A x C) (synCsb B x C)) hyp_csbeq1d_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_csbid`. -/
@[expose]
noncomputable def gCsbid (x : Var) (A : Class) :
    Nominal.NPrf (.classEq (synCsb (.cv x) x A) A) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCsb x y (.cv x) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @gSbsbc (.classMem (.cv y) A) x x
  have p0002 := @gSbid (.classMem (.cv y) A) x
  have p0003 :=
    @gBitr3i (synWsbc (.cv x) x (.classMem (.cv y) A))
      (synWsb x x (.classMem (.cv y) A)) (.classMem (.cv y) A) p0001 p0002
  have p0004 :=
    @gAbbii (synWsbc (.cv x) x (.classMem (.cv y) A)) (.classMem (.cv y) A) y p0003
  have p0005 :=
    @gAbid2 y A
      (by
        first
        | (aesop))
  have p0006 :=
    @gN3eqtri (synCsb (.cv x) x A) (.cab y (synWsbc (.cv x) x (.classMem (.cv y) A)))
      (.cab y (.classMem (.cv y) A)) A p0000 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_csbeq1a`. -/
@[expose]
noncomputable def gCsbeq1a (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B (synCsb A x B))) :=
  by
  have p0000 := @gCsbid x B
  have p0001 := @gCsbeq1 x (.cv x) A B
  have p0002 :=
    @gSyl5eqr (.classEq (.cv x) A) B (synCsb (.cv x) x B) (synCsb A x B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_csbeq2d`. -/
@[expose]
noncomputable def gCsbeq2d (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (hyp_csbeq2d_1 : Nominal.NPrf (synWnf x ph))
    (hyp_csbeq2d_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq (synCsb A x B) (synCsb A x C))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gEleq2d ph B C (.cv y) hyp_csbeq2d_2
  have p0001 :=
    @gSbcbid ph (.classMem (.cv y) B) (.classMem (.cv y) C) x A hyp_csbeq2d_1 p0000
  have p0002 :=
    @gAbbidv ph (synWsbc A x (.classMem (.cv y) B)) (synWsbc A x (.classMem (.cv y) C))
      y
      (by
        first
        | (aesop))
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCsb x y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCsb x y A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gN3eqtr4g ph (.cab y (synWsbc A x (.classMem (.cv y) B)))
      (.cab y (synWsbc A x (.classMem (.cv y) C))) (synCsb A x B) (synCsb A x C) p0002
      p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_csbeq2dv`. -/
@[expose]
noncomputable def gCsbeq2dv (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_csbeq2dv_1 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq (synCsb A x B) (synCsb A x C))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gCsbeq2d ph x A B C p0000 hyp_csbeq2dv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfcsb1d`. -/
@[expose]
noncomputable def gNfcsb1d (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfcsb1d_1 : Nominal.NPrf (.imp ph (synWnfc x A))) :
    Nominal.NPrf (.imp ph (synWnfc x (synCsb A x B))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCsb x y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0002 := @gNfsbc1d ph (.classMem (.cv y) B) x A hyp_nfcsb1d_1
  have p0003 := @gNfabd ph (synWsbc A x (.classMem (.cv y) B)) x y p0001 p0002
  have p0004 :=
    @gNfcxfrd ph x (synCsb A x B) (.cab y (synWsbc A x (.classMem (.cv y) B))) p0000
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfcsb1`. -/
@[expose]
noncomputable def gNfcsb1 (x : Var) (A : Class) (B : Class)
    (hyp_nfcsb1_1 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf (synWnfc x (synCsb A x B)) :=
  by
  have p0000 := @gA1i (synWnfc x A) synWtru hyp_nfcsb1_1
  have p0001 := @gNfcsb1d synWtru x A B p0000
  have p0002 := @gTrud (synWnfc x (synCsb A x B)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfcsb1v`. -/
@[expose]
noncomputable def gNfcsb1v (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWnfc x (synCsb A x B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 := @gNfcsb1 x A B p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfcsbd`. -/
@[expose]
noncomputable def gNfcsbd (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_nfcsbd_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfcsbd_2 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_nfcsbd_3 : Nominal.NPrf (.imp ph (synWnfc x B))) :
    Nominal.NPrf (.imp ph (synWnfc x (synCsb A y B))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
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
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCsb y z A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ph z
      (by
        first
        | (aesop))
  have p0002 :=
    @gNfcrd ph x z B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_nfcsbd_3
  have p0003 := @gNfsbcd ph (.classMem (.cv z) B) x y A hyp_nfcsbd_1 hyp_nfcsbd_2 p0002
  have p0004 := @gNfabd ph (synWsbc A y (.classMem (.cv z) B)) x z p0001 p0003
  have p0005 :=
    @gNfcxfrd ph x (synCsb A y B) (.cab z (synWsbc A y (.classMem (.cv z) B))) p0000
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfcsb`. -/
@[expose]
noncomputable def gNfcsb (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_nfcsb_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfcsb_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnfc x (synCsb A y B)) :=
  by
  have p0000 := @gNftru y
  have p0001 := @gA1i (synWnfc x A) synWtru hyp_nfcsb_1
  have p0002 := @gA1i (synWnfc x B) synWtru hyp_nfcsb_2
  have p0003 := @gNfcsbd synWtru x y A B p0000 p0001 p0002
  have p0004 := @gTrud (synWnfc x (synCsb A y B)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_csbiebt`. -/
@[expose]
noncomputable def gCsbiebt (x : Var) (A : Class) (B : Class) (C : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (synWnfc x C))
        (synWb (.all x (.imp (.classEq (.cv x) A) (.classEq B C)))
          (.classEq (synCsb A x B) C))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  have p0000 := @gElex A V
  have p0001 := @gSpsbc (.imp (.classEq (.cv x) A) (.classEq B C)) x A (synCvv)
  have p0002 :=
    @gAdantr (.classMem A (synCvv))
      (.imp (.all x (.imp (.classEq (.cv x) A) (.classEq B C)))
        (synWsbc A x (.imp (.classEq (.cv x) A) (.classEq B C))))
      (synWnfc x C) p0001
  have p0003 := @gSimpl (.classMem A (synCvv)) (synWnfc x C)
  have p0004 := @gBiimt (.classEq (.cv x) A) (.classEq B C)
  have p0005 := @gCsbeq1a x A B
  have p0006 := @gEqeq1d (.classEq (.cv x) A) B (synCsb A x B) C p0005
  have p0007 :=
    @gBitr3d (.classEq (.cv x) A) (.classEq B C)
      (.imp (.classEq (.cv x) A) (.classEq B C)) (.classEq (synCsb A x B) C) p0004 p0006
  have p0008 :=
    @gAdantl (.classEq (.cv x) A)
      (synWb (.imp (.classEq (.cv x) A) (.classEq B C)) (.classEq (synCsb A x B) C))
      (synWa (.classMem A (synCvv)) (synWnfc x C)) p0007
  have p0009 :=
    @gNfv (.classMem A (synCvv)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
  have p0010 := @gNfnfc1 x C
  have p0011 := @gNfan (.classMem A (synCvv)) (synWnfc x C) x p0009 p0010
  have p0012 :=
    @gNfcsb1v x A B
      (by
        first
        | (aesop))
  have p0013 :=
    @gA1i (synWnfc x (synCsb A x B)) (synWa (.classMem A (synCvv)) (synWnfc x C))
      p0012
  have p0014 := @gSimpr (.classMem A (synCvv)) (synWnfc x C)
  have p0015 :=
    @gNfeqd (synWa (.classMem A (synCvv)) (synWnfc x C)) x (synCsb A x B) C p0013
      p0014
  have p0016 :=
    @gSbciedf (synWa (.classMem A (synCvv)) (synWnfc x C))
      (.imp (.classEq (.cv x) A) (.classEq B C)) (.classEq (synCsb A x B) C) x A
      (synCvv)
      (by
        first
        | (aesop))
      p0003 p0008 p0011 p0015
  have p0017 :=
    @gSylibd (synWa (.classMem A (synCvv)) (synWnfc x C))
      (.all x (.imp (.classEq (.cv x) A) (.classEq B C)))
      (synWsbc A x (.imp (.classEq (.cv x) A) (.classEq B C)))
      (.classEq (synCsb A x B) C) p0002 p0016
  have p0018 := @gA1i (synWnfc x (synCsb A x B)) (synWnfc x C) p0012
  have p0019 := @gId (synWnfc x C)
  have p0020 := @gNfeqd (synWnfc x C) x (synCsb A x B) C p0018 p0019
  have p0021 := @gNfan1 (synWnfc x C) (.classEq (synCsb A x B) C) x p0010 p0020
  have p0022 :=
    @gBiimprcd (.classEq (.cv x) A) (.classEq B C) (.classEq (synCsb A x B) C) p0006
  have p0023 :=
    @gAdantl (.classEq (synCsb A x B) C) (.imp (.classEq (.cv x) A) (.classEq B C))
      (synWnfc x C) p0022
  have p0024 :=
    @gAlrimi (synWa (synWnfc x C) (.classEq (synCsb A x B) C))
      (.imp (.classEq (.cv x) A) (.classEq B C)) x p0021 p0023
  have p0025 :=
    @gEx (synWnfc x C) (.classEq (synCsb A x B) C)
      (.all x (.imp (.classEq (.cv x) A) (.classEq B C))) p0024
  have p0026 :=
    @gAdantl (synWnfc x C)
      (.imp (.classEq (synCsb A x B) C) (.all x (.imp (.classEq (.cv x) A) (.classEq B C))))
      (.classMem A (synCvv)) p0025
  have p0027 :=
    @gImpbid (synWa (.classMem A (synCvv)) (synWnfc x C))
      (.all x (.imp (.classEq (.cv x) A) (.classEq B C))) (.classEq (synCsb A x B) C)
      p0017 p0026
  have p0028 :=
    @gSylan (.classMem A V) (.classMem A (synCvv)) (synWnfc x C)
      (synWb (.all x (.imp (.classEq (.cv x) A) (.classEq B C))) (.classEq (synCsb A x B) C))
      p0000 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_csbiedf`. -/
@[expose]
noncomputable def gCsbiedf (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (V : Class) (dv_A_x : x ∉ A.fv) (hyp_csbiedf_1 : Nominal.NPrf (synWnf x ph))
    (hyp_csbiedf_2 : Nominal.NPrf (.imp ph (synWnfc x C)))
    (hyp_csbiedf_3 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_csbiedf_4 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq (synCsb A x B) C)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  have p0000 := @gEx ph (.classEq (.cv x) A) (.classEq B C) hyp_csbiedf_4
  have p0001 :=
    @gAlrimi ph (.imp (.classEq (.cv x) A) (.classEq B C)) x hyp_csbiedf_1 p0000
  have p0002 :=
    @gCsbiebt x A B C V
      (by
        first
        | (aesop))
  have p0003 :=
    @gSyl2anc ph (.classMem A V) (synWnfc x C)
      (synWb (.all x (.imp (.classEq (.cv x) A) (.classEq B C))) (.classEq (synCsb A x B) C))
      hyp_csbiedf_3 hyp_csbiedf_2 p0002
  have p0004 :=
    @gMpbid ph (.all x (.imp (.classEq (.cv x) A) (.classEq B C)))
      (.classEq (synCsb A x B) C) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_csbied`. -/
@[expose]
noncomputable def gCsbied (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (V : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_csbied_1 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_csbied_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq (synCsb A x B) C)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfcvd ph x C
      (by
        first
        | (aesop))
  have p0002 :=
    @gCsbiedf ph x A B C V
      (by
        first
        | (aesop))
      p0000 p0001 hyp_csbied_1 hyp_csbied_2
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elning`. -/
@[expose]
noncomputable def gElning (A : Class) (B : Class) (C : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classMem A (synCnin B C))
          (synWnan (.classMem A B) (.classMem A C)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gEleq1 (.cv x) A B
  have p0001 := @gEleq1 (.cv x) A C
  have p0002 :=
    @gNanbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B)
      (.classMem (.cv x) C) (.classMem A C) p0000 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNin x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @gElab2g (synWnan (.classMem (.cv x) B) (.classMem (.cv x) C))
      (synWnan (.classMem A B) (.classMem A C)) x A (synCnin B C) V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wnan,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union] at ⊢;
            aesop))
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_elcomplg`. -/
@[expose]
noncomputable def gElcomplg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classMem A (synCcompl B)) (.neg (.classMem A B)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCcompl B))
  have p0001 := @gEleq2i (synCcompl B) (synCnin B B) A p0000
  have p0002 := @gElning A B B V
  have p0003 := (Nominal.biimpRefl (synWnan (.classMem A B) (.classMem A B)))
  have p0004 := @gAnidm (.classMem A B)
  have p0005 :=
    @gXchbinx (synWnan (.classMem A B) (.classMem A B))
      (synWa (.classMem A B) (.classMem A B)) (.classMem A B) p0003 p0004
  have p0006 :=
    @gSyl6bb (.classMem A V) (.classMem A (synCnin B B))
      (synWnan (.classMem A B) (.classMem A B)) (.neg (.classMem A B)) p0002 p0005
  have p0007 :=
    @gSyl5bb (.classMem A (synCcompl B)) (.classMem A (synCnin B B)) (.classMem A V)
      (.neg (.classMem A B)) p0001 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_elin`. -/
@[expose]
noncomputable def gElin (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem A (synCin B C)) (synWa (.classMem A B) (.classMem A C))) :=
  by
  have p0000 := @gElex A (synCin B C)
  have p0001 := @gElex A B
  have p0002 := @gAdantr (.classMem A B) (.classMem A (synCvv)) (.classMem A C) p0001
  have p0003 := @gElcomplg A (synCnin B C) (synCvv)
  have p0004 := @gElning A B C (synCvv)
  have p0005 :=
    @gNotbid (.classMem A (synCvv)) (.classMem A (synCnin B C))
      (synWnan (.classMem A B) (.classMem A C)) p0004
  have p0006 :=
    @gBitrd (.classMem A (synCvv)) (.classMem A (synCcompl (synCnin B C)))
      (.neg (.classMem A (synCnin B C)))
      (.neg (synWnan (.classMem A B) (.classMem A C))) p0003 p0005
  have p0007 := (Nominal.classEqRefl (synCin B C))
  have p0008 := @gEleq2i (synCin B C) (synCcompl (synCnin B C)) A p0007
  have p0009 := (Nominal.biimpRefl (synWnan (.classMem A B) (.classMem A C)))
  have p0010 :=
    @gCon2bii (synWnan (.classMem A B) (.classMem A C))
      (synWa (.classMem A B) (.classMem A C)) p0009
  have p0011 :=
    @gN3bitr4g (.classMem A (synCvv)) (.classMem A (synCcompl (synCnin B C)))
      (.neg (synWnan (.classMem A B) (.classMem A C))) (.classMem A (synCin B C))
      (synWa (.classMem A B) (.classMem A C)) p0006 p0008 p0010
  have p0012 :=
    @gPm521nii (.classMem A (synCin B C)) (.classMem A (synCvv))
      (synWa (.classMem A B) (.classMem A C)) p0000 p0002 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_elun`. -/
@[expose]
noncomputable def gElun (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem A (synCun B C)) (synWo (.classMem A B) (.classMem A C))) :=
  by
  have p0000 := @gElex A (synCun B C)
  have p0001 := @gElex A B
  have p0002 := @gElex A C
  have p0003 :=
    @gJaoi (.classMem A B) (.classMem A (synCvv)) (.classMem A C) p0001 p0002
  have p0004 := @gElning A (synCcompl B) (synCcompl C) (synCvv)
  have p0005 := @gElcomplg A B (synCvv)
  have p0006 := @gElcomplg A C (synCvv)
  have p0007 :=
    @gNanbi12d (.classMem A (synCvv)) (.classMem A (synCcompl B))
      (.neg (.classMem A B)) (.classMem A (synCcompl C)) (.neg (.classMem A C)) p0005
      p0006
  have p0008 :=
    @gBitrd (.classMem A (synCvv))
      (.classMem A (synCnin (synCcompl B) (synCcompl C)))
      (synWnan (.classMem A (synCcompl B)) (.classMem A (synCcompl C)))
      (synWnan (.neg (.classMem A B)) (.neg (.classMem A C))) p0004 p0007
  have p0009 := (Nominal.classEqRefl (synCun B C))
  have p0010 := @gEleq2i (synCun B C) (synCnin (synCcompl B) (synCcompl C)) A p0009
  have p0011 := @gOran (.classMem A B) (.classMem A C)
  have p0012 :=
    (Nominal.biimpRefl (synWnan (.neg (.classMem A B)) (.neg (.classMem A C))))
  have p0013 :=
    @gBitr4i (synWo (.classMem A B) (.classMem A C))
      (.neg (synWa (.neg (.classMem A B)) (.neg (.classMem A C))))
      (synWnan (.neg (.classMem A B)) (.neg (.classMem A C))) p0011 p0012
  have p0014 :=
    @gN3bitr4g (.classMem A (synCvv))
      (.classMem A (synCnin (synCcompl B) (synCcompl C)))
      (synWnan (.neg (.classMem A B)) (.neg (.classMem A C))) (.classMem A (synCun B C))
      (synWo (.classMem A B) (.classMem A C)) p0008 p0010 p0013
  have p0015 :=
    @gPm521nii (.classMem A (synCun B C)) (.classMem A (synCvv))
      (synWo (.classMem A B) (.classMem A C)) p0000 p0003 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_eldif`. -/
@[expose]
noncomputable def gEldif (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem A (synCdif B C)) (synWa (.classMem A B) (.neg (.classMem A C)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCdif B C))
  have p0001 := @gEleq2i (synCdif B C) (synCin B (synCcompl C)) A p0000
  have p0002 := @gElin A B (synCcompl C)
  have p0003 := @gElcomplg A C B
  have p0004 :=
    @gPm532i (.classMem A B) (.classMem A (synCcompl C)) (.neg (.classMem A C)) p0003
  have p0005 :=
    @gN3bitri (.classMem A (synCdif B C)) (.classMem A (synCin B (synCcompl C)))
      (synWa (.classMem A B) (.classMem A (synCcompl C)))
      (synWa (.classMem A B) (.neg (.classMem A C))) p0001 p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_elsymdif`. -/
@[expose]
noncomputable def gElsymdif (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem A (synCsymdif B C))
        (.neg (synWb (.classMem A B) (.classMem A C)))) :=
  by
  have p0000 := @gElun A (synCdif B C) (synCdif C B)
  have p0001 := @gEldif A B C
  have p0002 := @gEldif A C B
  have p0003 :=
    @gOrbi12i (.classMem A (synCdif B C))
      (synWa (.classMem A B) (.neg (.classMem A C))) (.classMem A (synCdif C B))
      (synWa (.classMem A C) (.neg (.classMem A B))) p0001 p0002
  have p0004 :=
    @gBitri (.classMem A (synCun (synCdif B C) (synCdif C B)))
      (synWo (.classMem A (synCdif B C)) (.classMem A (synCdif C B)))
      (synWo (synWa (.classMem A B) (.neg (.classMem A C)))
        (synWa (.classMem A C) (.neg (.classMem A B))))
      p0000 p0003
  have p0005 := (Nominal.classEqRefl (synCsymdif B C))
  have p0006 :=
    @gEleq2i (synCsymdif B C) (synCun (synCdif B C) (synCdif C B)) A p0005
  have p0007 := @gXor (.classMem A B) (.classMem A C)
  have p0008 :=
    @gN3bitr4i (.classMem A (synCun (synCdif B C) (synCdif C B)))
      (synWo (synWa (.classMem A B) (.neg (.classMem A C)))
        (synWa (.classMem A C) (.neg (.classMem A B))))
      (.classMem A (synCsymdif B C)) (.neg (synWb (.classMem A B) (.classMem A C)))
      p0004 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_elnin`. -/
@[expose]
noncomputable def gElnin (A : Class) (B : Class) (C : Class)
    (hyp_elbool_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem A (synCnin B C)) (synWnan (.classMem A B) (.classMem A C))) :=
  by
  have p0000 := @gElning A B C (synCvv)
  have p0001 := Nominal.mp hyp_elbool_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elcompl`. -/
@[expose]
noncomputable def gElcompl (A : Class) (B : Class)
    (hyp_elbool_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (.classMem A (synCcompl B)) (.neg (.classMem A B))) :=
  by
  have p0000 := @gElcomplg A B (synCvv)
  have p0001 := Nominal.mp hyp_elbool_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nincom`. -/
@[expose]
noncomputable def gNincom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCnin A B) (synCnin B A)) :=
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
  have p0000 := @gNancom (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @gVex x
  have p0002 := @gElnin (.cv x) A B p0001
  have p0003 := @gElnin (.cv x) B A p0001
  have p0004 :=
    @gN3bitr4i (synWnan (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWnan (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.classMem (.cv x) (synCnin A B)) (.classMem (.cv x) (synCnin B A)) p0000 p0002
      p0003
  have p0005 :=
    @gEqriv x (synCnin A B) (synCnin B A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              Finset.mem_union] at ⊢;
            aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_dblcompl`. -/
@[expose]
noncomputable def gDblcompl (A : Class) :
    Nominal.NPrf (.classEq (synCcompl (synCcompl A)) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @gVex x
  have p0001 := @gElcompl (.cv x) (synCcompl A) p0000
  have p0002 := @gElcompl (.cv x) A p0000
  have p0003 := @gCon2bii (.classMem (.cv x) (synCcompl A)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @gBitr4i (.classMem (.cv x) (synCcompl (synCcompl A)))
      (.neg (.classMem (.cv x) (synCcompl A))) (.classMem (.cv x) A) p0001 p0003
  have p0005 :=
    @gEqriv x (synCcompl (synCcompl A)) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfnin`. -/
@[expose]
noncomputable def gNfnin (x : Var) (A : Class) (B : Class)
    (hyp_nfnin_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfnin_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnfc x (synCnin A B)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNin y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfel2 x (.cv y) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      hyp_nfnin_1
  have p0002 :=
    @gNfel2 x (.cv y) B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      hyp_nfnin_2
  have p0003 := @gNfnan (.classMem (.cv y) A) (.classMem (.cv y) B) x p0001 p0002
  have p0004 := @gNfab (synWnan (.classMem (.cv y) A) (.classMem (.cv y) B)) x y p0003
  have p0005 :=
    @gNfcxfr x (synCnin A B)
      (.cab y (synWnan (.classMem (.cv y) A) (.classMem (.cv y) B))) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfcompl`. -/
@[expose]
noncomputable def gNfcompl (x : Var) (A : Class)
    (hyp_nfbool_1 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf (synWnfc x (synCcompl A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCcompl A))
  have p0001 := @gNfnin x A A hyp_nfbool_1 hyp_nfbool_1
  have p0002 := @gNfcxfr x (synCcompl A) (synCnin A A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfun`. -/
@[expose]
noncomputable def gNfun (x : Var) (A : Class) (B : Class)
    (hyp_nfbool_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfbool_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnfc x (synCun A B)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCun A B))
  have p0001 := @gNfcompl x A hyp_nfbool_1
  have p0002 := @gNfcompl x B hyp_nfbool_2
  have p0003 := @gNfnin x (synCcompl A) (synCcompl B) p0001 p0002
  have p0004 :=
    @gNfcxfr x (synCun A B) (synCnin (synCcompl A) (synCcompl B)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nineq1`. -/
@[expose]
noncomputable def gNineq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCnin A C) (synCnin B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gEleq2 A B (.cv x)
  have p0001 :=
    @gNanbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @gAbbidv (.classEq A B) (synWnan (.classMem (.cv x) A) (.classMem (.cv x) C))
      (synWnan (.classMem (.cv x) B) (.classMem (.cv x) C)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNin x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNin x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gN3eqtr4g (.classEq A B)
      (.cab x (synWnan (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (.cab x (synWnan (.classMem (.cv x) B) (.classMem (.cv x) C))) (synCnin A C)
      (synCnin B C) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nineq2`. -/
@[expose]
noncomputable def gNineq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCnin C A) (synCnin C B))) :=
  by
  have p0000 := @gNineq1 A B C
  have p0001 := @gNincom A C
  have p0002 := @gNincom B C
  have p0003 :=
    @gN3eqtr3g (.classEq A B) (synCnin A C) (synCnin B C) (synCnin C A)
      (synCnin C B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nineq12`. -/
@[expose]
noncomputable def gNineq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (.classEq (synCnin A C) (synCnin B D))) :=
  by
  have p0000 := @gNineq1 A B C
  have p0001 := @gNineq2 C D B
  have p0002 :=
    @gSylan9eq (.classEq A B) (.classEq C D) (synCnin A C) (synCnin B C) (synCnin B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nineq12i`. -/
@[expose]
noncomputable def gNineq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_nineqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_nineq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCnin A C) (synCnin B D)) :=
  by
  have p0000 := @gNineq12 A B C D
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (.classEq (synCnin A C) (synCnin B D))
      hyp_nineqi_1 hyp_nineq12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nineq2d`. -/
@[expose]
noncomputable def gNineq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_nineqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCnin C A) (synCnin C B))) :=
  by
  have p0000 := @gNineq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCnin C A) (synCnin C B)) hyp_nineqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_compleq`. -/
@[expose]
noncomputable def gCompleq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCcompl A) (synCcompl B))) :=
  by
  have p0000 := @gNineq12 A B A B
  have p0001 := @gAnidms (.classEq A B) (.classEq (synCnin A A) (synCnin B B)) p0000
  have p0002 := (Nominal.classEqRefl (synCcompl A))
  have p0003 := (Nominal.classEqRefl (synCcompl B))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCnin A A) (synCnin B B) (synCcompl A)
      (synCcompl B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_compleqi`. -/
@[expose]
noncomputable def gCompleqi (A : Class) (B : Class)
    (hyp_compleqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCcompl A) (synCcompl B)) :=
  by
  have p0000 := @gCompleq A B
  have p0001 := Nominal.mp hyp_compleqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_compleqd`. -/
@[expose]
noncomputable def gCompleqd (ph : Wff) (A : Class) (B : Class)
    (hyp_compleqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCcompl A) (synCcompl B))) :=
  by
  have p0000 := @gCompleq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCcompl A) (synCcompl B)) hyp_compleqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_difeq1`. -/
@[expose]
noncomputable def gDifeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCdif A C) (synCdif B C))) :=
  by
  have p0000 := @gNineq1 A B (synCcompl C)
  have p0001 :=
    @gCompleqd (.classEq A B) (synCnin A (synCcompl C)) (synCnin B (synCcompl C))
      p0000
  have p0002 := (Nominal.classEqRefl (synCdif A C))
  have p0003 := (Nominal.classEqRefl (synCin A (synCcompl C)))
  have p0004 :=
    @gEqtri (synCdif A C) (synCin A (synCcompl C))
      (synCcompl (synCnin A (synCcompl C))) p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCdif B C))
  have p0006 := (Nominal.classEqRefl (synCin B (synCcompl C)))
  have p0007 :=
    @gEqtri (synCdif B C) (synCin B (synCcompl C))
      (synCcompl (synCnin B (synCcompl C))) p0005 p0006
  have p0008 :=
    @gN3eqtr4g (.classEq A B) (synCcompl (synCnin A (synCcompl C)))
      (synCcompl (synCnin B (synCcompl C))) (synCdif A C) (synCdif B C) p0001 p0004
      p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_difeq2`. -/
@[expose]
noncomputable def gDifeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCdif C A) (synCdif C B))) :=
  by
  have p0000 := @gCompleq A B
  have p0001 := @gNineq2d (.classEq A B) (synCcompl A) (synCcompl B) C p0000
  have p0002 :=
    @gCompleqd (.classEq A B) (synCnin C (synCcompl A)) (synCnin C (synCcompl B))
      p0001
  have p0003 := (Nominal.classEqRefl (synCdif C A))
  have p0004 := (Nominal.classEqRefl (synCin C (synCcompl A)))
  have p0005 :=
    @gEqtri (synCdif C A) (synCin C (synCcompl A))
      (synCcompl (synCnin C (synCcompl A))) p0003 p0004
  have p0006 := (Nominal.classEqRefl (synCdif C B))
  have p0007 := (Nominal.classEqRefl (synCin C (synCcompl B)))
  have p0008 :=
    @gEqtri (synCdif C B) (synCin C (synCcompl B))
      (synCcompl (synCnin C (synCcompl B))) p0006 p0007
  have p0009 :=
    @gN3eqtr4g (.classEq A B) (synCcompl (synCnin C (synCcompl A)))
      (synCcompl (synCnin C (synCcompl B))) (synCdif C A) (synCdif C B) p0002 p0005
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_dfss`. -/
@[expose]
noncomputable def gDfss (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (.classEq A (synCin A B))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWss A B))
  have p0001 := @gEqcom (synCin A B) A
  have p0002 :=
    @gBitri (synWss A B) (.classEq (synCin A B) A) (.classEq A (synCin A B)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dfss2`. -/
@[expose]
noncomputable def gDfss2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (synWss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @gDfss A B
  have p0001 :=
    @gDfcleq x A (synCin A B)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
  have p0002 := @gElin (.cv x) A B
  have p0003 :=
    @gBibi2i (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @gAlbii (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCin A B)))
      (synWb (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      x p0003
  have p0005 :=
    @gBitri (.classEq A (synCin A B))
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCin A B))))
      (.all x (synWb (.classMem (.cv x) A)
          (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))))
      p0001 p0004
  have p0006 :=
    @gBitri (synWss A B) (.classEq A (synCin A B))
      (.all x (synWb (.classMem (.cv x) A)
          (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))))
      p0000 p0005
  have p0007 := @gPm471 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0008 :=
    @gAlbii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      x p0007
  have p0009 :=
    @gBitr4i (synWss A B)
      (.all x (synWb (.classMem (.cv x) A)
          (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_dfss3`. -/
@[expose]
noncomputable def gDfss3 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (synWb (synWss A B) (synWral x A (.classMem (.cv x) B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (synWral x A (.classMem (.cv x) B)))
  have p0002 :=
    @gBitr4i (synWss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWral x A (.classMem (.cv x) B)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dfss2f`. -/
@[expose]
noncomputable def gDfss2f (x : Var) (A : Class) (B : Class)
    (hyp_dfss2f_1 : Nominal.NPrf (synWnfc x A))
    (hyp_dfss2f_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf
      (synWb (synWss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @gDfss2 z A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfcri x z A
      (by
        first
        | (aesop))
      hyp_dfss2f_1
  have p0002 :=
    @gNfcri x z B
      (by
        first
        | (aesop))
      hyp_dfss2f_2
  have p0003 := @gNfim (.classMem (.cv z) A) (.classMem (.cv z) B) x p0001 p0002
  have p0004 :=
    @gNfv (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @gEleq1 (.cv z) (.cv x) A
  have p0006 := @gEleq1 (.cv z) (.cv x) B
  have p0007 :=
    @gImbi12d (.classEq (.cv z) (.cv x)) (.classMem (.cv z) A) (.classMem (.cv x) A)
      (.classMem (.cv z) B) (.classMem (.cv x) B) p0005 p0006
  have p0008_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (synWb (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))
          (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gCbval (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) z x p0003 p0004 p0008_e02_recanon
  have p0009 :=
    @gBitri (synWss A B) (.all z (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_ssel`. -/
@[expose]
noncomputable def gSsel (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (.imp (.classMem C A) (.classMem C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gBiimpi (synWss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0000
  have p0002 :=
    @gN1921bi (synWss A B) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0001
  have p0003 :=
    @gAnim2d (synWss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classEq (.cv x) C) p0002
  have p0004 :=
    @gEximdv (synWss A B) (synWa (.classEq (.cv x) C) (.classMem (.cv x) A))
      (synWa (.classEq (.cv x) C) (.classMem (.cv x) B)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0003
  have p0005 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x C A (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0006 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x C B (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0007 :=
    @gN3imtr4g (synWss A B)
      (synWex x (synWa (.classEq (.cv x) C) (.classMem (.cv x) A)))
      (synWex x (synWa (.classEq (.cv x) C) (.classMem (.cv x) B))) (.classMem C A)
      (.classMem C B) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ssel2`. -/
@[expose]
noncomputable def gSsel2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWa (synWss A B) (.classMem C A)) (.classMem C B)) :=
  by
  have p0000 := @gSsel A B C
  have p0001 := @gImp (synWss A B) (.classMem C A) (.classMem C B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseli`. -/
@[expose]
noncomputable def gSseli (A : Class) (B : Class) (C : Class)
    (hyp_sseli_1 : Nominal.NPrf (synWss A B)) :
    Nominal.NPrf (.imp (.classMem C A) (.classMem C B)) :=
  by
  have p0000 := @gSsel A B C
  have p0001 := Nominal.mp hyp_sseli_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sselii`. -/
@[expose]
noncomputable def gSselii (A : Class) (B : Class) (C : Class)
    (hyp_sseli_1 : Nominal.NPrf (synWss A B))
    (hyp_sselii_2 : Nominal.NPrf (.classMem C A)) : Nominal.NPrf (.classMem C B) :=
  by
  have p0000 := @gSseli A B C hyp_sseli_1
  have p0001 := Nominal.mp hyp_sselii_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseldi`. -/
@[expose]
noncomputable def gSseldi (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseli_1 : Nominal.NPrf (synWss A B))
    (hyp_sseldi_2 : Nominal.NPrf (.imp ph (.classMem C A))) :
    Nominal.NPrf (.imp ph (.classMem C B)) :=
  by
  have p0000 := @gSseli A B C hyp_sseli_1
  have p0001 := @gSyl ph (.classMem C A) (.classMem C B) hyp_sseldi_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseld`. -/
@[expose]
noncomputable def gSseld (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseld_1 : Nominal.NPrf (.imp ph (synWss A B))) :
    Nominal.NPrf (.imp ph (.imp (.classMem C A) (.classMem C B))) :=
  by
  have p0000 := @gSsel A B C
  have p0001 :=
    @gSyl ph (synWss A B) (.imp (.classMem C A) (.classMem C B)) hyp_sseld_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sselda`. -/
@[expose]
noncomputable def gSselda (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseld_1 : Nominal.NPrf (.imp ph (synWss A B))) :
    Nominal.NPrf (.imp (synWa ph (.classMem C A)) (.classMem C B)) :=
  by
  have p0000 := @gSseld ph A B C hyp_sseld_1
  have p0001 := @gImp ph (.classMem C A) (.classMem C B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseldd`. -/
@[expose]
noncomputable def gSseldd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseld_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_sseldd_2 : Nominal.NPrf (.imp ph (.classMem C A))) :
    Nominal.NPrf (.imp ph (.classMem C B)) :=
  by
  have p0000 := @gSseld ph A B C hyp_sseld_1
  have p0001 := @gMpd ph (.classMem C A) (.classMem C B) hyp_sseldd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssriv`. -/
@[expose]
noncomputable def gSsriv (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv)
    (hyp_ssriv_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) :
    Nominal.NPrf (synWss A B) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gMpgbir (synWss A B) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0000
      hyp_ssriv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssrdv`. -/
@[expose]
noncomputable def gSsrdv (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_ssrdv_1 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :
    Nominal.NPrf (.imp ph (synWss A B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gAlrimiv ph (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      (by
        first
        | (aesop))
      hyp_ssrdv_1
  have p0001 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @gSylibr ph (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (synWss A B)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sstr2`. -/
@[expose]
noncomputable def gSstr2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (.imp (synWss B C) (synWss A C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gSsel A B (.cv x)
  have p0001 :=
    @gImim1d (synWss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @gAlimdv (synWss A B) (.imp (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0001
  have p0003 :=
    @gDfss2 x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @gDfss2 x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gN3imtr4g (synWss A B) (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))) (synWss B C)
      (synWss A C) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_sstr`. -/
@[expose]
noncomputable def gSstr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWa (synWss A B) (synWss B C)) (synWss A C)) :=
  by
  have p0000 := @gSstr2 A B C
  have p0001 := @gImp (synWss A B) (synWss B C) (synWss A C) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sstri`. -/
@[expose]
noncomputable def gSstri (A : Class) (B : Class) (C : Class)
    (hyp_sstri_1 : Nominal.NPrf (synWss A B))
    (hyp_sstri_2 : Nominal.NPrf (synWss B C)) : Nominal.NPrf (synWss A C) :=
  by
  have p0000 := @gSstr2 A B C
  have p0001 :=
    @gMp2 (synWss A B) (synWss B C) (synWss A C) hyp_sstri_1 hyp_sstri_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sstrd`. -/
@[expose]
noncomputable def gSstrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sstrd_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_sstrd_2 : Nominal.NPrf (.imp ph (synWss B C))) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gSstr A B C
  have p0001 :=
    @gSyl2anc ph (synWss A B) (synWss B C) (synWss A C) hyp_sstrd_1 hyp_sstrd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5ss`. -/
@[expose]
noncomputable def gSyl5ss (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5ss_1 : Nominal.NPrf (synWss A B))
    (hyp_syl5ss_2 : Nominal.NPrf (.imp ph (synWss B C))) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gA1i (synWss A B) ph hyp_syl5ss_1
  have p0001 := @gSstrd ph A B C p0000 hyp_syl5ss_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6ss`. -/
@[expose]
noncomputable def gSyl6ss (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6ss_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_syl6ss_2 : Nominal.NPrf (synWss B C)) : Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gA1i (synWss B C) ph hyp_syl6ss_2
  have p0001 := @gSstrd ph A B C hyp_syl6ss_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan9ss`. -/
@[expose]
noncomputable def gSylan9ss (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sylan9ss_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_sylan9ss_2 : Nominal.NPrf (.imp ps (synWss B C))) :
    Nominal.NPrf (.imp (synWa ph ps) (synWss A C)) :=
  by
  have p0000 := @gSstr A B C
  have p0001 :=
    @gSyl2an ph (synWss A B) (synWss B C) (synWss A C) ps hyp_sylan9ss_1
      hyp_sylan9ss_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqss`. -/
@[expose]
noncomputable def gEqss (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.classEq A B) (synWa (synWss A B) (synWss B A))) :=
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
  have p0000 := @gAlbiim (.classMem (.cv x) A) (.classMem (.cv x) B) x
  have p0001 :=
    @gDfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @gDfss2 x B A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @gAnbi12i (synWss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWss B A) (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))) p0002
      p0003
  have p0005 :=
    @gN3bitr4i (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWa (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))))
      (.classEq A B) (synWa (synWss A B) (synWss B A)) p0000 p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_eqssi`. -/
@[expose]
noncomputable def gEqssi (A : Class) (B : Class)
    (hyp_eqssi_1 : Nominal.NPrf (synWss A B))
    (hyp_eqssi_2 : Nominal.NPrf (synWss B A)) : Nominal.NPrf (.classEq A B) :=
  by
  have p0000 := @gEqss A B
  have p0001 :=
    @gMpbir2an (.classEq A B) (synWss A B) (synWss B A) hyp_eqssi_1 hyp_eqssi_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqssd`. -/
@[expose]
noncomputable def gEqssd (ph : Wff) (A : Class) (B : Class)
    (hyp_eqssd_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_eqssd_2 : Nominal.NPrf (.imp ph (synWss B A))) :
    Nominal.NPrf (.imp ph (.classEq A B)) :=
  by
  have p0000 := @gEqss A B
  have p0001 :=
    @gSylanbrc ph (synWss A B) (synWss B A) (.classEq A B) hyp_eqssd_1 hyp_eqssd_2
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssid`. -/
@[expose]
noncomputable def gSsid (A : Class) : Nominal.NPrf (synWss A A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @gId (.classMem (.cv x) A)
  have p0001 :=
    @gSsriv x A A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssv`. -/
@[expose]
noncomputable def gSsv (A : Class) : Nominal.NPrf (synWss A (synCvv)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @gElex (.cv x) A
  have p0001 :=
    @gSsriv x A (synCvv)
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
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseq1`. -/
@[expose]
noncomputable def gSseq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWss A C) (synWss B C))) :=
  by
  have p0000 := @gEqss A B
  have p0001 := @gSstr2 B A C
  have p0002 :=
    @gAdantl (synWss B A) (.imp (synWss A C) (synWss B C)) (synWss A B) p0001
  have p0003 := @gSstr2 A B C
  have p0004 :=
    @gAdantr (synWss A B) (.imp (synWss B C) (synWss A C)) (synWss B A) p0003
  have p0005 :=
    @gImpbid (synWa (synWss A B) (synWss B A)) (synWss A C) (synWss B C) p0002 p0004
  have p0006 :=
    @gSylbi (.classEq A B) (synWa (synWss A B) (synWss B A))
      (synWb (synWss A C) (synWss B C)) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_sseq2`. -/
@[expose]
noncomputable def gSseq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWss C A) (synWss C B))) :=
  by
  have p0000 := @gSstr2 C A B
  have p0001 := @gCom12 (synWss C A) (synWss A B) (synWss C B) p0000
  have p0002 := @gSstr2 C B A
  have p0003 := @gCom12 (synWss C B) (synWss B A) (synWss C A) p0002
  have p0004 :=
    @gAnim12i (synWss A B) (.imp (synWss C A) (synWss C B)) (synWss B A)
      (.imp (synWss C B) (synWss C A)) p0001 p0003
  have p0005 := @gEqss A B
  have p0006 := @gDfbi2 (synWss C A) (synWss C B)
  have p0007 :=
    @gN3imtr4i (synWa (synWss A B) (synWss B A))
      (synWa (.imp (synWss C A) (synWss C B)) (.imp (synWss C B) (synWss C A)))
      (.classEq A B) (synWb (synWss C A) (synWss C B)) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_sseq12`. -/
@[expose]
noncomputable def gSseq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (synWb (synWss A C) (synWss B D))) :=
  by
  have p0000 := @gSseq1 A B C
  have p0001 := @gSseq2 C D B
  have p0002 :=
    @gSylan9bb (.classEq A B) (synWss A C) (synWss B C) (.classEq C D) (synWss B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sseq1i`. -/
@[expose]
noncomputable def gSseq1i (A : Class) (B : Class) (C : Class)
    (hyp_sseq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWss A C) (synWss B C)) :=
  by
  have p0000 := @gSseq1 A B C
  have p0001 := Nominal.mp hyp_sseq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseq2i`. -/
@[expose]
noncomputable def gSseq2i (A : Class) (B : Class) (C : Class)
    (hyp_sseq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWss C A) (synWss C B)) :=
  by
  have p0000 := @gSseq2 A B C
  have p0001 := Nominal.mp hyp_sseq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseq12i`. -/
@[expose]
noncomputable def gSseq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_sseq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_sseq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (synWb (synWss A C) (synWss B D)) :=
  by
  have p0000 := @gSseq12 A B C D
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (synWb (synWss A C) (synWss B D))
      hyp_sseq1i_1 hyp_sseq12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseq1d`. -/
@[expose]
noncomputable def gSseq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWss A C) (synWss B C))) :=
  by
  have p0000 := @gSseq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWss A C) (synWss B C)) hyp_sseq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseq2d`. -/
@[expose]
noncomputable def gSseq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWss C A) (synWss C B))) :=
  by
  have p0000 := @gSseq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWss C A) (synWss C B)) hyp_sseq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseq12d`. -/
@[expose]
noncomputable def gSseq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_sseq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_sseq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (synWb (synWss A C) (synWss B D))) :=
  by
  have p0000 := @gSseq1d ph A B C hyp_sseq1d_1
  have p0001 := @gSseq2d ph C D B hyp_sseq12d_2
  have p0002 := @gBitrd ph (synWss A C) (synWss B C) (synWss B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqsstri`. -/
@[expose]
noncomputable def gEqsstri (A : Class) (B : Class) (C : Class)
    (hyp_eqsstr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqsstr_2 : Nominal.NPrf (synWss B C)) : Nominal.NPrf (synWss A C) :=
  by
  have p0000 := @gSseq1i A B C hyp_eqsstr_1
  have p0001 := @gMpbir (synWss A C) (synWss B C) hyp_eqsstr_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqsstr3i`. -/
@[expose]
noncomputable def gEqsstr3i (A : Class) (B : Class) (C : Class)
    (hyp_eqsstr3_1 : Nominal.NPrf (.classEq B A))
    (hyp_eqsstr3_2 : Nominal.NPrf (synWss B C)) : Nominal.NPrf (synWss A C) :=
  by
  have p0000 := @gEqcomi B A hyp_eqsstr3_1
  have p0001 := @gEqsstri A B C p0000 hyp_eqsstr3_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseqtri`. -/
@[expose]
noncomputable def gSseqtri (A : Class) (B : Class) (C : Class)
    (hyp_sseqtr_1 : Nominal.NPrf (synWss A B))
    (hyp_sseqtr_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (synWss A C) :=
  by
  have p0000 := @gSseq2i B C A hyp_sseqtr_2
  have p0001 := @gMpbi (synWss A B) (synWss A C) hyp_sseqtr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseqtr4i`. -/
@[expose]
noncomputable def gSseqtr4i (A : Class) (B : Class) (C : Class)
    (hyp_sseqtr4_1 : Nominal.NPrf (synWss A B))
    (hyp_sseqtr4_2 : Nominal.NPrf (.classEq C B)) : Nominal.NPrf (synWss A C) :=
  by
  have p0000 := @gEqcomi C B hyp_sseqtr4_2
  have p0001 := @gSseqtri A B C hyp_sseqtr4_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqsstrd`. -/
@[expose]
noncomputable def gEqsstrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqsstrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqsstrd_2 : Nominal.NPrf (.imp ph (synWss B C))) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gSseq1d ph A B C hyp_eqsstrd_1
  have p0001 := @gMpbird ph (synWss A C) (synWss B C) hyp_eqsstrd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqsstr3d`. -/
@[expose]
noncomputable def gEqsstr3d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqsstr3d_1 : Nominal.NPrf (.imp ph (.classEq B A)))
    (hyp_eqsstr3d_2 : Nominal.NPrf (.imp ph (synWss B C))) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gEqcomd ph B A hyp_eqsstr3d_1
  have p0001 := @gEqsstrd ph A B C p0000 hyp_eqsstr3d_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseqtrd`. -/
@[expose]
noncomputable def gSseqtrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseqtrd_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_sseqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gSseq2d ph B C A hyp_sseqtrd_2
  have p0001 := @gMpbid ph (synWss A B) (synWss A C) hyp_sseqtrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sseqtr4d`. -/
@[expose]
noncomputable def gSseqtr4d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseqtr4d_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_sseqtr4d_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gEqcomd ph C B hyp_sseqtr4d_2
  have p0001 := @gSseqtrd ph A B C hyp_sseqtr4d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3sstr4i`. -/
@[expose]
noncomputable def gN3sstr4i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3sstr4_1 : Nominal.NPrf (synWss A B))
    (hyp_n_3sstr4_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3sstr4_3 : Nominal.NPrf (.classEq D B)) : Nominal.NPrf (synWss C D) :=
  by
  have p0000 := @gSseq12i C A D B hyp_n_3sstr4_2 hyp_n_3sstr4_3
  have p0001 := @gMpbir (synWss C D) (synWss A B) hyp_n_3sstr4_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3sstr4g`. -/
@[expose]
noncomputable def gN3sstr4g (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3sstr4g_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_n_3sstr4g_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3sstr4g_3 : Nominal.NPrf (.classEq D B)) :
    Nominal.NPrf (.imp ph (synWss C D)) :=
  by
  have p0000 := @gSseq12i C A D B hyp_n_3sstr4g_2 hyp_n_3sstr4g_3
  have p0001 := @gSylibr ph (synWss A B) (synWss C D) hyp_n_3sstr4g_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3sstr4d`. -/
@[expose]
noncomputable def gN3sstr4d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3sstr4d_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_n_3sstr4d_2 : Nominal.NPrf (.imp ph (.classEq C A)))
    (hyp_n_3sstr4d_3 : Nominal.NPrf (.imp ph (.classEq D B))) :
    Nominal.NPrf (.imp ph (synWss C D)) :=
  by
  have p0000 := @gSseq12d ph C A D B hyp_n_3sstr4d_2 hyp_n_3sstr4d_3
  have p0001 := @gMpbird ph (synWss C D) (synWss A B) hyp_n_3sstr4d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eqss`. -/
@[expose]
noncomputable def gSyl5eqss (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqss_1 : Nominal.NPrf (.classEq A B))
    (hyp_syl5eqss_2 : Nominal.NPrf (.imp ph (synWss B C))) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gSseq1i A B C hyp_syl5eqss_1
  have p0001 := @gSylibr ph (synWss B C) (synWss A C) hyp_syl5eqss_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eqssr`. -/
@[expose]
noncomputable def gSyl5eqssr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqssr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5eqssr_2 : Nominal.NPrf (.imp ph (synWss B C))) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gEqcomi B A hyp_syl5eqssr_1
  have p0001 := @gSyl5eqss ph A B C p0000 hyp_syl5eqssr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6sseq`. -/
@[expose]
noncomputable def gSyl6sseq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6sseq_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_syl6sseq_2 : Nominal.NPrf (.classEq B C)) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gSseq2i B C A hyp_syl6sseq_2
  have p0001 := @gSylib ph (synWss A B) (synWss A C) hyp_syl6sseq_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6sseqr`. -/
@[expose]
noncomputable def gSyl6sseqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6ssr_1 : Nominal.NPrf (.imp ph (synWss A B)))
    (hyp_syl6ssr_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gEqcomi C B hyp_syl6ssr_2
  have p0001 := @gSyl6sseq ph A B C hyp_syl6ssr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5sseq`. -/
@[expose]
noncomputable def gSyl5sseq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5sseq_1 : Nominal.NPrf (synWss B A))
    (hyp_syl5sseq_2 : Nominal.NPrf (.imp ph (.classEq A C))) :
    Nominal.NPrf (.imp ph (synWss B C)) :=
  by
  have p0000 := @gSseq2 A C B
  have p0001 := @gBiimpa (.classEq A C) (synWss B A) (synWss B C) p0000
  have p0002 :=
    @gSylancl ph (.classEq A C) (synWss B A) (synWss B C) hyp_syl5sseq_2 hyp_syl5sseq_1
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_syl5sseqr`. -/
@[expose]
noncomputable def gSyl5sseqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5sseqr_1 : Nominal.NPrf (synWss B A))
    (hyp_syl5sseqr_2 : Nominal.NPrf (.imp ph (.classEq C A))) :
    Nominal.NPrf (.imp ph (synWss B C)) :=
  by
  have p0000 := @gA1i (synWss B A) ph hyp_syl5sseqr_1
  have p0001 := @gSseqtr4d ph B A C p0000 hyp_syl5sseqr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6eqss`. -/
@[expose]
noncomputable def gSyl6eqss (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eqss_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eqss_2 : Nominal.NPrf (synWss B C)) :
    Nominal.NPrf (.imp ph (synWss A C)) :=
  by
  have p0000 := @gA1i (synWss B C) ph hyp_syl6eqss_2
  have p0001 := @gEqsstrd ph A B C hyp_syl6eqss_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqimss`. -/
@[expose]
noncomputable def gEqimss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWss A B)) :=
  by
  have p0000 := @gEqss A B
  have p0001 := @gSimplbi (.classEq A B) (synWss A B) (synWss B A) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqimss2`. -/
@[expose]
noncomputable def gEqimss2 (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq B A) (synWss A B)) :=
  by
  have p0000 := @gEqimss A B
  have p0001 := @gEqcoms (synWss A B) A B p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqimssi`. -/
@[expose]
noncomputable def gEqimssi (A : Class) (B : Class)
    (hyp_eqimssi_1 : Nominal.NPrf (.classEq A B)) : Nominal.NPrf (synWss A B) :=
  by
  have p0000 := @gSsid A
  have p0001 := @gSseqtri A A B p0000 hyp_eqimssi_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nss`. -/
@[expose]
noncomputable def gNss (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.neg (synWss A B))
        (synWex x (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @gExanali (.classMem (.cv x) A) (.classMem (.cv x) B) x
  have p0001 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @gXchbinxr (synWex x (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (synWss A B) p0000
      p0001
  have p0003 :=
    @gBicomi (synWex x (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))
      (.neg (synWss A B)) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ss2ab`. -/
@[expose]
noncomputable def gSs2ab (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWss (.cab x ph) (.cab x ps)) (.all x (.imp ph ps))) :=
  by
  have p0000 := @gNfab1 ph x
  have p0001 := @gNfab1 ps x
  have p0002 := @gDfss2f x (.cab x ph) (.cab x ps) p0000 p0001
  have p0003 := @gAbid ph x
  have p0004 := @gAbid ps x
  have p0005 :=
    @gImbi12i (.classMem (.cv x) (.cab x ph)) ph (.classMem (.cv x) (.cab x ps)) ps p0003
      p0004
  have p0006 :=
    @gAlbii (.imp (.classMem (.cv x) (.cab x ph)) (.classMem (.cv x) (.cab x ps)))
      (.imp ph ps) x p0005
  have p0007 :=
    @gBitri (synWss (.cab x ph) (.cab x ps))
      (.all x (.imp (.classMem (.cv x) (.cab x ph)) (.classMem (.cv x) (.cab x ps))))
      (.all x (.imp ph ps)) p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_abss`. -/
@[expose]
noncomputable def gAbss (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (synWss (.cab x ph) A) (.all x (.imp ph (.classMem (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gAbid2 x A
      (by
        first
        | (aesop))
  have p0001 := @gSseq2i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0000
  have p0002 := @gSs2ab ph (.classMem (.cv x) A) x
  have p0003 :=
    @gBitr3i (synWss (.cab x ph) A) (synWss (.cab x ph) (.cab x (.classMem (.cv x) A)))
      (.all x (.imp ph (.classMem (.cv x) A))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ssab`. -/
@[expose]
noncomputable def gSsab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (synWss A (.cab x ph)) (.all x (.imp (.classMem (.cv x) A) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gAbid2 x A
      (by
        first
        | (aesop))
  have p0001 := @gSseq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0000
  have p0002 := @gSs2ab (.classMem (.cv x) A) ph x
  have p0003 :=
    @gBitr3i (synWss A (.cab x ph)) (synWss (.cab x (.classMem (.cv x) A)) (.cab x ph))
      (.all x (.imp (.classMem (.cv x) A) ph)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ss2abi`. -/
@[expose]
noncomputable def gSs2abi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_ss2abi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (synWss (.cab x ph) (.cab x ps)) :=
  by
  have p0000 := @gSs2ab ph ps x
  have p0001 :=
    @gMpgbir (synWss (.cab x ph) (.cab x ps)) (.imp ph ps) x p0000 hyp_ss2abi_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ss2abdv`. -/
@[expose]
noncomputable def gSs2abdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_ss2abdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (synWss (.cab x ps) (.cab x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gAlrimiv ph (.imp ps ch) x
      (by
        first
        | (aesop))
      hyp_ss2abdv_1
  have p0001 := @gSs2ab ps ch x
  have p0002 :=
    @gSylibr ph (.all x (.imp ps ch)) (synWss (.cab x ps) (.cab x ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_abssdv`. -/
@[expose]
noncomputable def gAbssdv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_abssdv_1 : Nominal.NPrf (.imp ph (.imp ps (.classMem (.cv x) A)))) :
    Nominal.NPrf (.imp ph (synWss (.cab x ps) A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gAlrimiv ph (.imp ps (.classMem (.cv x) A)) x
      (by
        first
        | (aesop))
      hyp_abssdv_1
  have p0001 :=
    @gAbss ps x A
      (by
        first
        | (aesop))
  have p0002 :=
    @gSylibr ph (.all x (.imp ps (.classMem (.cv x) A))) (synWss (.cab x ps) A) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_abssi`. -/
@[expose]
noncomputable def gAbssi (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_abssi_1 : Nominal.NPrf (.imp ph (.classMem (.cv x) A))) :
    Nominal.NPrf (synWss (.cab x ph) A) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @gSs2abi ph (.classMem (.cv x) A) x hyp_abssi_1
  have p0001 :=
    @gAbid2 x A
      (by
        first
        | (aesop))
  have p0002 := @gSseqtri (.cab x ph) (.cab x (.classMem (.cv x) A)) A p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ssab2`. -/
@[expose]
noncomputable def gSsab2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWss (.cab x (synWa (.classMem (.cv x) A) ph)) A) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @gSimpl (.classMem (.cv x) A) ph
  have p0001 :=
    @gAbssi (synWa (.classMem (.cv x) A) ph) x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssrab2`. -/
@[expose]
noncomputable def gSsrab2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWss (synCrab x A ph) A) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.classEqRefl (synCrab x A ph))
  have p0001 :=
    @gSsab2 ph x A
      (by
        first
        | (aesop))
  have p0002 :=
    @gEqsstri (synCrab x A ph) (.cab x (synWa (.classMem (.cv x) A) ph)) A p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dfpss2`. -/
@[expose]
noncomputable def gDfpss2 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWpss A B) (synWa (synWss A B) (.neg (.classEq A B)))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWpss A B))
  have p0001 := (Nominal.biimpRefl (synWne A B))
  have p0002 := @gAnbi2i (synWne A B) (.neg (.classEq A B)) (synWss A B) p0001
  have p0003 :=
    @gBitri (synWpss A B) (synWa (synWss A B) (synWne A B))
      (synWa (synWss A B) (.neg (.classEq A B))) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_dfpss3`. -/
@[expose]
noncomputable def gDfpss3 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWpss A B) (synWa (synWss A B) (.neg (synWss B A)))) :=
  by
  have p0000 := @gDfpss2 A B
  have p0001 := @gEqss A B
  have p0002 := @gBaib (.classEq A B) (synWss A B) (synWss B A) p0001
  have p0003 := @gNotbid (synWss A B) (.classEq A B) (synWss B A) p0002
  have p0004 := @gPm532i (synWss A B) (.neg (.classEq A B)) (.neg (synWss B A)) p0003
  have p0005 :=
    @gBitri (synWpss A B) (synWa (synWss A B) (.neg (.classEq A B)))
      (synWa (synWss A B) (.neg (synWss B A))) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_pssss`. -/
@[expose]
noncomputable def gPssss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWpss A B) (synWss A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWpss A B))
  have p0001 := @gSimplbi (synWpss A B) (synWss A B) (synWne A B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pssssd`. -/
@[expose]
noncomputable def gPssssd (ph : Wff) (A : Class) (B : Class)
    (hyp_pssssd_1 : Nominal.NPrf (.imp ph (synWpss A B))) :
    Nominal.NPrf (.imp ph (synWss A B)) :=
  by
  have p0000 := @gPssss A B
  have p0001 := @gSyl ph (synWpss A B) (synWss A B) hyp_pssssd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sspss`. -/
@[expose]
noncomputable def gSspss (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (synWo (synWpss A B) (.classEq A B))) :=
  by
  have p0000 := @gDfpss2 A B
  have p0001 := @gSimplbi2 (synWpss A B) (synWss A B) (.neg (.classEq A B)) p0000
  have p0002 := @gCon1d (synWss A B) (.classEq A B) (synWpss A B) p0001
  have p0003 := @gOrrd (synWss A B) (synWpss A B) (.classEq A B) p0002
  have p0004 := @gPssss A B
  have p0005 := @gEqimss A B
  have p0006 := @gJaoi (synWpss A B) (synWss A B) (.classEq A B) p0004 p0005
  have p0007 := @gImpbii (synWss A B) (synWo (synWpss A B) (.classEq A B)) p0003 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_difeq1i`. -/
@[expose]
noncomputable def gDifeq1i (A : Class) (B : Class) (C : Class)
    (hyp_difeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCdif A C) (synCdif B C)) :=
  by
  have p0000 := @gDifeq1 A B C
  have p0001 := Nominal.mp hyp_difeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_difeq2i`. -/
@[expose]
noncomputable def gDifeq2i (A : Class) (B : Class) (C : Class)
    (hyp_difeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCdif C A) (synCdif C B)) :=
  by
  have p0000 := @gDifeq2 A B C
  have p0001 := Nominal.mp hyp_difeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_difeq1d`. -/
@[expose]
noncomputable def gDifeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_difeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCdif A C) (synCdif B C))) :=
  by
  have p0000 := @gDifeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCdif A C) (synCdif B C)) hyp_difeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_difeq2d`. -/
@[expose]
noncomputable def gDifeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_difeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCdif C A) (synCdif C B))) :=
  by
  have p0000 := @gDifeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCdif C A) (synCdif C B)) hyp_difeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_difeq12d`. -/
@[expose]
noncomputable def gDifeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_difeq12d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_difeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCdif A C) (synCdif B D))) :=
  by
  have p0000 := @gDifeq1d ph A B C hyp_difeq12d_1
  have p0001 := @gDifeq2d ph C D B hyp_difeq12d_2
  have p0002 := @gEqtrd ph (synCdif A C) (synCdif B C) (synCdif B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_difeqri`. -/
@[expose]
noncomputable def gDifeqri (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (hyp_difeqri_1 : Nominal.NPrf
        (synWb (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (.classMem (.cv x) C))) :
    Nominal.NPrf (.classEq (synCdif A B) C) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @gEldif (.cv x) A B
  have p0001 :=
    @gBitri (.classMem (.cv x) (synCdif A B))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) C)
      p0000 hyp_difeqri_1
  have p0002 :=
    @gEqriv x (synCdif A B) C
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eldifi`. -/
@[expose]
noncomputable def gEldifi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (synCdif B C)) (.classMem A B)) :=
  by
  have p0000 := @gEldif A B C
  have p0001 :=
    @gSimplbi (.classMem A (synCdif B C)) (.classMem A B) (.neg (.classMem A C)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eldifn`. -/
@[expose]
noncomputable def gEldifn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (synCdif B C)) (.neg (.classMem A C))) :=
  by
  have p0000 := @gEldif A B C
  have p0001 :=
    @gSimprbi (.classMem A (synCdif B C)) (.classMem A B) (.neg (.classMem A C)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_difdif`. -/
@[expose]
noncomputable def gDifdif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCdif A (synCdif B A)) A) :=
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
  have p0000 := @gPm445im (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @gIman (.classMem (.cv x) B) (.classMem (.cv x) A)
  have p0002 := @gEldif (.cv x) B A
  have p0003 :=
    @gXchbinxr (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))
      (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A)))
      (.classMem (.cv x) (synCdif B A)) p0001 p0002
  have p0004 :=
    @gAnbi2i (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.neg (.classMem (.cv x) (synCdif B A))) (.classMem (.cv x) A) p0003
  have p0005 :=
    @gBitr2i (.classMem (.cv x) A)
      (synWa (.classMem (.cv x) A) (.imp (.classMem (.cv x) B) (.classMem (.cv x) A)))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCdif B A)))) p0000 p0004
  have p0006 :=
    @gDifeqri x A (synCdif B A) A
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_difss`. -/
@[expose]
noncomputable def gDifss (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCdif A B) A) :=
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
  have p0000 := @gEldifi (.cv x) A B
  have p0001 :=
    @gSsriv x (synCdif A B) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ddif`. -/
@[expose]
noncomputable def gDdif (A : Class) :
    Nominal.NPrf (.classEq (synCdif (synCvv) (synCdif (synCvv) A)) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @gVex x
  have p0001 := @gEldif (.cv x) (synCvv) A
  have p0002 :=
    @gMpbiran (.classMem (.cv x) (synCdif (synCvv) A)) (.classMem (.cv x) (synCvv))
      (.neg (.classMem (.cv x) A)) p0000 p0001
  have p0003 :=
    @gCon2bii (.classMem (.cv x) (synCdif (synCvv) A)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @gBiantrur (.classMem (.cv x) (synCvv))
      (.neg (.classMem (.cv x) (synCdif (synCvv) A))) p0000
  have p0005 :=
    @gBitr2i (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCdif (synCvv) A)))
      (synWa (.classMem (.cv x) (synCvv)) (.neg (.classMem (.cv x) (synCdif (synCvv) A))))
      p0003 p0004
  have p0006 :=
    @gDifeqri x (synCvv) (synCdif (synCvv) A) A
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
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ssdif`. -/
@[expose]
noncomputable def gSsdif (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCdif A C) (synCdif B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gSsel A B (.cv x)
  have p0001 :=
    @gAnim1d (synWss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.neg (.classMem (.cv x) C)) p0000
  have p0002 := @gEldif (.cv x) A C
  have p0003 := @gEldif (.cv x) B C
  have p0004 :=
    @gN3imtr4g (synWss A B) (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) C)))
      (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) C)))
      (.classMem (.cv x) (synCdif A C)) (.classMem (.cv x) (synCdif B C)) p0001 p0002
      p0003
  have p0005 :=
    @gSsrdv (synWss A B) x (synCdif A C) (synCdif B C)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_uneqri`. -/
@[expose]
noncomputable def gUneqri (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (hyp_uneqri_1 : Nominal.NPrf (synWb (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
          (.classMem (.cv x) C))) :
    Nominal.NPrf (.classEq (synCun A B) C) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @gElun (.cv x) A B
  have p0001 :=
    @gBitri (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0000
      hyp_uneqri_1
  have p0002 :=
    @gEqriv x (synCun A B) C
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_unidm`. -/
@[expose]
noncomputable def gUnidm (A : Class) : Nominal.NPrf (.classEq (synCun A A) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @gOridm (.classMem (.cv x) A)
  have p0001 :=
    @gUneqri x A A A
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

/-- Checked nominal proof certificate identified upstream as `g_uncom`. -/
@[expose]
noncomputable def gUncom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCun A B) (synCun B A)) :=
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
  have p0000 := @gOrcom (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @gElun (.cv x) B A
  have p0002 :=
    @gBitr4i (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWo (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.classMem (.cv x) (synCun B A)) p0000 p0001
  have p0003 :=
    @gUneqri x A B (synCun B A)
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
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_uneq1`. -/
@[expose]
noncomputable def gUneq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCun A C) (synCun B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gEleq2 A B (.cv x)
  have p0001 :=
    @gOrbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 := @gElun (.cv x) A C
  have p0003 := @gElun (.cv x) B C
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWo (.classMem (.cv x) A) (.classMem (.cv x) C))
      (synWo (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.classMem (.cv x) (synCun A C)) (.classMem (.cv x) (synCun B C)) p0001 p0002
      p0003
  have p0005 :=
    @gEqrdv (.classEq A B) x (synCun A C) (synCun B C)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_uneq2`. -/
@[expose]
noncomputable def gUneq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCun C A) (synCun C B))) :=
  by
  have p0000 := @gUneq1 A B C
  have p0001 := @gUncom C A
  have p0002 := @gUncom C B
  have p0003 :=
    @gN3eqtr4g (.classEq A B) (synCun A C) (synCun B C) (synCun C A) (synCun C B)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_uneq12`. -/
@[expose]
noncomputable def gUneq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (.classEq (synCun A C) (synCun B D))) :=
  by
  have p0000 := @gUneq1 A B C
  have p0001 := @gUneq2 C D B
  have p0002 :=
    @gSylan9eq (.classEq A B) (.classEq C D) (synCun A C) (synCun B C) (synCun B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_uneq1i`. -/
@[expose]
noncomputable def gUneq1i (A : Class) (B : Class) (C : Class)
    (hyp_uneq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCun A C) (synCun B C)) :=
  by
  have p0000 := @gUneq1 A B C
  have p0001 := Nominal.mp hyp_uneq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_uneq2i`. -/
@[expose]
noncomputable def gUneq2i (A : Class) (B : Class) (C : Class)
    (hyp_uneq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCun C A) (synCun C B)) :=
  by
  have p0000 := @gUneq2 A B C
  have p0001 := Nominal.mp hyp_uneq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_uneq12i`. -/
@[expose]
noncomputable def gUneq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_uneq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_uneq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCun A C) (synCun B D)) :=
  by
  have p0000 := @gUneq12 A B C D
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (.classEq (synCun A C) (synCun B D))
      hyp_uneq1i_1 hyp_uneq12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_uneq1d`. -/
@[expose]
noncomputable def gUneq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_uneq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCun A C) (synCun B C))) :=
  by
  have p0000 := @gUneq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCun A C) (synCun B C)) hyp_uneq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_uneq2d`. -/
@[expose]
noncomputable def gUneq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_uneq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCun C A) (synCun C B))) :=
  by
  have p0000 := @gUneq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCun C A) (synCun C B)) hyp_uneq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_uneq12d`. -/
@[expose]
noncomputable def gUneq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_uneq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_uneq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCun A C) (synCun B D))) :=
  by
  have p0000 := @gUneq12 A B C D
  have p0001 :=
    @gSyl2anc ph (.classEq A B) (.classEq C D) (.classEq (synCun A C) (synCun B D))
      hyp_uneq1d_1 hyp_uneq12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_unass`. -/
@[expose]
noncomputable def gUnass (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCun (synCun A B) C) (synCun A (synCun B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gElun (.cv x) A (synCun B C)
  have p0001 := @gElun (.cv x) B C
  have p0002 :=
    @gOrbi2i (.classMem (.cv x) (synCun B C))
      (synWo (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0001
  have p0003 := @gElun (.cv x) A B
  have p0004 :=
    @gOrbi1i (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0003
  have p0005 := @gOrass (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0006 :=
    @gBitr2i (synWo (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) C))
      (synWo (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (synWo (.classMem (.cv x) A) (synWo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      p0004 p0005
  have p0007 :=
    @gN3bitrri (.classMem (.cv x) (synCun A (synCun B C)))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) (synCun B C)))
      (synWo (.classMem (.cv x) A) (synWo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (synWo (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) C)) p0000 p0002 p0006
  have p0008 :=
    @gUneqri x (synCun A B) C (synCun A (synCun B C))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_ssun1`. -/
@[expose]
noncomputable def gSsun1 (A : Class) (B : Class) :
    Nominal.NPrf (synWss A (synCun A B)) :=
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
  have p0000 := @gOrc (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @gElun (.cv x) A B
  have p0002 :=
    @gSylibr (.classMem (.cv x) A) (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classMem (.cv x) (synCun A B)) p0000 p0001
  have p0003 :=
    @gSsriv x A (synCun A B)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ssun2`. -/
@[expose]
noncomputable def gSsun2 (A : Class) (B : Class) :
    Nominal.NPrf (synWss A (synCun B A)) :=
  by
  have p0000 := @gSsun1 A B
  have p0001 := @gUncom A B
  have p0002 := @gSseqtri A (synCun A B) (synCun B A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ssun3`. -/
@[expose]
noncomputable def gSsun3 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss A (synCun B C))) :=
  by
  have p0000 := @gSsun1 B C
  have p0001 := @gSstr2 A B (synCun B C)
  have p0002 :=
    @gMpi (synWss A B) (synWss B (synCun B C)) (synWss A (synCun B C)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elun1`. -/
@[expose]
noncomputable def gElun1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem A (synCun B C))) :=
  by
  have p0000 := @gSsun1 B C
  have p0001 := @gSseli B (synCun B C) A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elun2`. -/
@[expose]
noncomputable def gElun2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem A (synCun C B))) :=
  by
  have p0000 := @gSsun2 B C
  have p0001 := @gSseli B (synCun C B) A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_unss1`. -/
@[expose]
noncomputable def gUnss1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCun A C) (synCun B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gSsel A B (.cv x)
  have p0001 :=
    @gOrim1d (synWss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 := @gElun (.cv x) A C
  have p0003 := @gElun (.cv x) B C
  have p0004 :=
    @gN3imtr4g (synWss A B) (synWo (.classMem (.cv x) A) (.classMem (.cv x) C))
      (synWo (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.classMem (.cv x) (synCun A C)) (.classMem (.cv x) (synCun B C)) p0001 p0002
      p0003
  have p0005 :=
    @gSsrdv (synWss A B) x (synCun A C) (synCun B C)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ssequn1`. -/
@[expose]
noncomputable def gSsequn1 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (.classEq (synCun A B) B)) :=
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
  have p0000 :=
    @gBicom (.classMem (.cv x) B) (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
  have p0001 := @gPm472 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0002 := @gElun (.cv x) A B
  have p0003 :=
    @gBibi1i (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) B) p0002
  have p0004 :=
    @gN3bitr4i
      (synWb (.classMem (.cv x) B) (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWb (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) B)) p0000 p0001 p0003
  have p0005 :=
    @gAlbii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) B)) x p0004
  have p0006 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0007 :=
    @gDfcleq x (synCun A B) B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @gN3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (synWb (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) B)))
      (synWss A B) (.classEq (synCun A B) B) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_unss2`. -/
@[expose]
noncomputable def gUnss2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCun C A) (synCun C B))) :=
  by
  have p0000 := @gUnss1 A B C
  have p0001 := @gUncom C A
  have p0002 := @gUncom C B
  have p0003 :=
    @gN3sstr4g (synWss A B) (synCun A C) (synCun B C) (synCun C A) (synCun C B)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_unss12`. -/
@[expose]
noncomputable def gUnss12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (synWss A B) (synWss C D)) (synWss (synCun A C) (synCun B D))) :=
  by
  have p0000 := @gUnss1 A B C
  have p0001 := @gUnss2 C D B
  have p0002 :=
    @gSylan9ss (synWss A B) (synWss C D) (synCun A C) (synCun B C) (synCun B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ssequn2`. -/
@[expose]
noncomputable def gSsequn2 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (.classEq (synCun B A) B)) :=
  by
  have p0000 := @gSsequn1 A B
  have p0001 := @gUncom A B
  have p0002 := @gEqeq1i (synCun A B) (synCun B A) B p0001
  have p0003 :=
    @gBitri (synWss A B) (.classEq (synCun A B) B) (.classEq (synCun B A) B) p0000
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_unss`. -/
@[expose]
noncomputable def gUnss (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (synWa (synWss A C) (synWss B C)) (synWss (synCun A B) C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @gDfss2 x (synCun A B) C
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gN1926 (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))
      (.imp (.classMem (.cv x) B) (.classMem (.cv x) C)) x
  have p0002 := @gElun (.cv x) A B
  have p0003 :=
    @gImbi1i (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0002
  have p0004 := @gJaob (.classMem (.cv x) A) (.classMem (.cv x) C) (.classMem (.cv x) B)
  have p0005 :=
    @gBitri (.imp (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) C))
      (.imp (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (synWa (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))
        (.imp (.classMem (.cv x) B) (.classMem (.cv x) C)))
      p0003 p0004
  have p0006 :=
    @gAlbii (.imp (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) C))
      (synWa (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))
        (.imp (.classMem (.cv x) B) (.classMem (.cv x) C)))
      x p0005
  have p0007 :=
    @gDfss2 x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @gDfss2 x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0009 :=
    @gAnbi12i (synWss A C) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (synWss B C) (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) C))) p0007
      p0008
  have p0010 :=
    @gN3bitr4i
      (.all x (synWa (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))
          (.imp (.classMem (.cv x) B) (.classMem (.cv x) C))))
      (synWa (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)))
        (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) C))))
      (.all x (.imp (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) C)))
      (synWa (synWss A C) (synWss B C)) p0001 p0006 p0009
  have p0011 :=
    @gBitr2i (synWss (synCun A B) C)
      (.all x (.imp (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) C)))
      (synWa (synWss A C) (synWss B C)) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_unssi`. -/
@[expose]
noncomputable def gUnssi (A : Class) (B : Class) (C : Class)
    (hyp_unssi_1 : Nominal.NPrf (synWss A C))
    (hyp_unssi_2 : Nominal.NPrf (synWss B C)) : Nominal.NPrf (synWss (synCun A B) C) :=
  by
  have p0000 := @gPm32i (synWss A C) (synWss B C) hyp_unssi_1 hyp_unssi_2
  have p0001 := @gUnss A B C
  have p0002 :=
    @gMpbi (synWa (synWss A C) (synWss B C)) (synWss (synCun A B) C) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_unssd`. -/
@[expose]
noncomputable def gUnssd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_unssd_1 : Nominal.NPrf (.imp ph (synWss A C)))
    (hyp_unssd_2 : Nominal.NPrf (.imp ph (synWss B C))) :
    Nominal.NPrf (.imp ph (synWss (synCun A B) C)) :=
  by
  have p0000 := @gUnss A B C
  have p0001 :=
    @gBiimpi (synWa (synWss A C) (synWss B C)) (synWss (synCun A B) C) p0000
  have p0002 :=
    @gSyl2anc ph (synWss A C) (synWss B C) (synWss (synCun A B) C) hyp_unssd_1
      hyp_unssd_2 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexun`. -/
@[expose]
noncomputable def gRexun (ph : Wff) (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (synWrex x (synCun A B) ph) (synWo (synWrex x A ph) (synWrex x B ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWrex x (synCun A B) ph))
  have p0001 :=
    @gN1943 (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) ph) x
  have p0002 := @gElun (.cv x) A B
  have p0003 :=
    @gAnbi1i (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) ph p0002
  have p0004 := @gAndir (.classMem (.cv x) A) (.classMem (.cv x) B) ph
  have p0005 :=
    @gBitri (synWa (.classMem (.cv x) (synCun A B)) ph)
      (synWa (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) ph)
      (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) ph)) p0003
      p0004
  have p0006 :=
    @gExbii (synWa (.classMem (.cv x) (synCun A B)) ph)
      (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) ph)) x p0005
  have p0007 := (Nominal.biimpRefl (synWrex x A ph))
  have p0008 := (Nominal.biimpRefl (synWrex x B ph))
  have p0009 :=
    @gOrbi12i (synWrex x A ph) (synWex x (synWa (.classMem (.cv x) A) ph))
      (synWrex x B ph) (synWex x (synWa (.classMem (.cv x) B) ph)) p0007 p0008
  have p0010 :=
    @gN3bitr4i
      (synWex x (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) ph)))
      (synWo (synWex x (synWa (.classMem (.cv x) A) ph))
        (synWex x (synWa (.classMem (.cv x) B) ph)))
      (synWex x (synWa (.classMem (.cv x) (synCun A B)) ph))
      (synWo (synWrex x A ph) (synWrex x B ph)) p0001 p0006 p0009
  have p0011 :=
    @gBitri (synWrex x (synCun A B) ph)
      (synWex x (synWa (.classMem (.cv x) (synCun A B)) ph))
      (synWo (synWrex x A ph) (synWrex x B ph)) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_ralunb`. -/
@[expose]
noncomputable def gRalunb (ph : Wff) (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (synWral x (synCun A B) ph) (synWa (synWral x A ph) (synWral x B ph))) :=
  by
  have p0000 := @gElun (.cv x) A B
  have p0001 :=
    @gImbi1i (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) ph p0000
  have p0002 := @gJaob (.classMem (.cv x) A) ph (.classMem (.cv x) B)
  have p0003 :=
    @gBitri (.imp (.classMem (.cv x) (synCun A B)) ph)
      (.imp (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) ph)
      (synWa (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ph)) p0001 p0002
  have p0004 :=
    @gAlbii (.imp (.classMem (.cv x) (synCun A B)) ph)
      (synWa (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ph)) x p0003
  have p0005 :=
    @gN1926 (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ph) x
  have p0006 :=
    @gBitri (.all x (.imp (.classMem (.cv x) (synCun A B)) ph))
      (.all x (synWa (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ph)))
      (synWa (.all x (.imp (.classMem (.cv x) A) ph)) (.all x (.imp (.classMem (.cv x) B) ph)))
      p0004 p0005
  have p0007 := (Nominal.biimpRefl (synWral x (synCun A B) ph))
  have p0008 := (Nominal.biimpRefl (synWral x A ph))
  have p0009 := (Nominal.biimpRefl (synWral x B ph))
  have p0010 :=
    @gAnbi12i (synWral x A ph) (.all x (.imp (.classMem (.cv x) A) ph))
      (synWral x B ph) (.all x (.imp (.classMem (.cv x) B) ph)) p0008 p0009
  have p0011 :=
    @gN3bitr4i (.all x (.imp (.classMem (.cv x) (synCun A B)) ph))
      (synWa (.all x (.imp (.classMem (.cv x) A) ph)) (.all x (.imp (.classMem (.cv x) B) ph)))
      (synWral x (synCun A B) ph) (synWa (synWral x A ph) (synWral x B ph)) p0006
      p0007 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_elin2`. -/
@[expose]
noncomputable def gElin2 (A : Class) (B : Class) (C : Class) (X : Class)
    (hyp_elin2_x : Nominal.NPrf (.classEq X (synCin B C))) :
    Nominal.NPrf (synWb (.classMem A X) (synWa (.classMem A B) (.classMem A C))) :=
  by
  have p0000 := @gEleq2i X (synCin B C) A hyp_elin2_x
  have p0001 := @gElin A B C
  have p0002 :=
    @gBitri (.classMem A X) (.classMem A (synCin B C))
      (synWa (.classMem A B) (.classMem A C)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_incom`. -/
@[expose]
noncomputable def gIncom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCin A B) (synCin B A)) :=
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
  have p0000 := @gAncom (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @gElin (.cv x) A B
  have p0002 := @gElin (.cv x) B A
  have p0003 :=
    @gN3bitr4i (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) (synCin B A)) p0000 p0001
      p0002
  have p0004 :=
    @gEqriv x (synCin A B) (synCin B A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ineqri`. -/
@[expose]
noncomputable def gIneqri (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (hyp_ineqri_1 : Nominal.NPrf (synWb (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
          (.classMem (.cv x) C))) :
    Nominal.NPrf (.classEq (synCin A B) C) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @gElin (.cv x) A B
  have p0001 :=
    @gBitri (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0000
      hyp_ineqri_1
  have p0002 :=
    @gEqriv x (synCin A B) C
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ineq1`. -/
@[expose]
noncomputable def gIneq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCin A C) (synCin B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gEleq2 A B (.cv x)
  have p0001 :=
    @gAnbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 := @gElin (.cv x) A C
  have p0003 := @gElin (.cv x) B C
  have p0004 :=
    @gN3bitr4g (.classEq A B) (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.classMem (.cv x) (synCin A C)) (.classMem (.cv x) (synCin B C)) p0001 p0002
      p0003
  have p0005 :=
    @gEqrdv (.classEq A B) x (synCin A C) (synCin B C)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ineq2`. -/
@[expose]
noncomputable def gIneq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCin C A) (synCin C B))) :=
  by
  have p0000 := @gIneq1 A B C
  have p0001 := @gIncom C A
  have p0002 := @gIncom C B
  have p0003 :=
    @gN3eqtr4g (.classEq A B) (synCin A C) (synCin B C) (synCin C A) (synCin C B)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ineq12`. -/
@[expose]
noncomputable def gIneq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (.classEq (synCin A C) (synCin B D))) :=
  by
  have p0000 := @gIneq1 A B C
  have p0001 := @gIneq2 C D B
  have p0002 :=
    @gSylan9eq (.classEq A B) (.classEq C D) (synCin A C) (synCin B C) (synCin B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ineq1i`. -/
@[expose]
noncomputable def gIneq1i (A : Class) (B : Class) (C : Class)
    (hyp_ineq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCin A C) (synCin B C)) :=
  by
  have p0000 := @gIneq1 A B C
  have p0001 := Nominal.mp hyp_ineq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ineq2i`. -/
@[expose]
noncomputable def gIneq2i (A : Class) (B : Class) (C : Class)
    (hyp_ineq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCin C A) (synCin C B)) :=
  by
  have p0000 := @gIneq2 A B C
  have p0001 := Nominal.mp hyp_ineq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ineq12i`. -/
@[expose]
noncomputable def gIneq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_ineq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_ineq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCin A C) (synCin B D)) :=
  by
  have p0000 := @gIneq12 A B C D
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (.classEq (synCin A C) (synCin B D))
      hyp_ineq1i_1 hyp_ineq12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ineq1d`. -/
@[expose]
noncomputable def gIneq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ineq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCin A C) (synCin B C))) :=
  by
  have p0000 := @gIneq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCin A C) (synCin B C)) hyp_ineq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ineq2d`. -/
@[expose]
noncomputable def gIneq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ineq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCin C A) (synCin C B))) :=
  by
  have p0000 := @gIneq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCin C A) (synCin C B)) hyp_ineq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ineq12d`. -/
@[expose]
noncomputable def gIneq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_ineq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_ineq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCin A C) (synCin B D))) :=
  by
  have p0000 := @gIneq12 A B C D
  have p0001 :=
    @gSyl2anc ph (.classEq A B) (.classEq C D) (.classEq (synCin A C) (synCin B D))
      hyp_ineq1d_1 hyp_ineq12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfss1`. -/
@[expose]
noncomputable def gDfss1 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (.classEq (synCin B A) A)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWss A B))
  have p0001 := @gIncom A B
  have p0002 := @gEqeq1i (synCin A B) (synCin B A) A p0001
  have p0003 :=
    @gBitri (synWss A B) (.classEq (synCin A B) A) (.classEq (synCin B A) A) p0000
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_inidm`. -/
@[expose]
noncomputable def gInidm (A : Class) : Nominal.NPrf (.classEq (synCin A A) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @gAnidm (.classMem (.cv x) A)
  have p0001 :=
    @gIneqri x A A A
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

/-- Checked nominal proof certificate identified upstream as `g_inass`. -/
@[expose]
noncomputable def gInass (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCin (synCin A B) C) (synCin A (synCin B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gAnass (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0001 := @gElin (.cv x) B C
  have p0002 :=
    @gAnbi2i (.classMem (.cv x) (synCin B C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0001
  have p0003 :=
    @gBitr4i
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (synWa (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) (synCin B C))) p0000 p0002
  have p0004 := @gElin (.cv x) A B
  have p0005 :=
    @gAnbi1i (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0004
  have p0006 := @gElin (.cv x) A (synCin B C)
  have p0007 :=
    @gN3bitr4i
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) (synCin B C)))
      (synWa (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) C))
      (.classMem (.cv x) (synCin A (synCin B C))) p0003 p0005 p0006
  have p0008 :=
    @gIneqri x (synCin A B) C (synCin A (synCin B C))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_in12`. -/
@[expose]
noncomputable def gIn12 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCin A (synCin B C)) (synCin B (synCin A C))) :=
  by
  have p0000 := @gIncom A B
  have p0001 := @gIneq1i (synCin A B) (synCin B A) C p0000
  have p0002 := @gInass A B C
  have p0003 := @gInass B A C
  have p0004 :=
    @gN3eqtr3i (synCin (synCin A B) C) (synCin (synCin B A) C)
      (synCin A (synCin B C)) (synCin B (synCin A C)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_in32`. -/
@[expose]
noncomputable def gIn32 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCin (synCin A B) C) (synCin (synCin A C) B)) :=
  by
  have p0000 := @gInass A B C
  have p0001 := @gIn12 A B C
  have p0002 := @gIncom B (synCin A C)
  have p0003 :=
    @gN3eqtri (synCin (synCin A B) C) (synCin A (synCin B C))
      (synCin B (synCin A C)) (synCin (synCin A C) B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_in4`. -/
@[expose]
noncomputable def gIn4 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.classEq (synCin (synCin A B) (synCin C D)) (synCin (synCin A C) (synCin B D))) :=
  by
  have p0000 := @gIn12 B C D
  have p0001 := @gIneq2i (synCin B (synCin C D)) (synCin C (synCin B D)) A p0000
  have p0002 := @gInass A B (synCin C D)
  have p0003 := @gInass A C (synCin B D)
  have p0004 :=
    @gN3eqtr4i (synCin A (synCin B (synCin C D)))
      (synCin A (synCin C (synCin B D))) (synCin (synCin A B) (synCin C D))
      (synCin (synCin A C) (synCin B D)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_inindi`. -/
@[expose]
noncomputable def gInindi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCin A (synCin B C)) (synCin (synCin A B) (synCin A C))) :=
  by
  have p0000 := @gInidm A
  have p0001 := @gIneq1i (synCin A A) A (synCin B C) p0000
  have p0002 := @gIn4 A A B C
  have p0003 :=
    @gEqtr3i (synCin (synCin A A) (synCin B C)) (synCin A (synCin B C))
      (synCin (synCin A B) (synCin A C)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sseqin2`. -/
@[expose]
noncomputable def gSseqin2 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (.classEq (synCin B A) A)) :=
  by
  have p0000 := @gDfss1 A B
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_inss1`. -/
@[expose]
noncomputable def gInss1 (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCin A B) A) :=
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
  have p0000 := @gElin (.cv x) A B
  have p0001 :=
    @gSimplbi (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) A)
      (.classMem (.cv x) B) p0000
  have p0002 :=
    @gSsriv x (synCin A B) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_inss2`. -/
@[expose]
noncomputable def gInss2 (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCin A B) B) :=
  by
  have p0000 := @gIncom B A
  have p0001 := @gInss1 B A
  have p0002 := @gEqsstr3i (synCin A B) (synCin B A) B p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ssin`. -/
@[expose]
noncomputable def gSsin (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (synWa (synWss A B) (synWss A C)) (synWss A (synCin B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gElin (.cv x) B C
  have p0001 :=
    @gImbi2i (.classMem (.cv x) (synCin B C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @gAlbii (.imp (.classMem (.cv x) A) (.classMem (.cv x) (synCin B C)))
      (.imp (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) (.classMem (.cv x) C))) x
      p0001
  have p0003 := @gJcab (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0004 :=
    @gAlbii
      (.imp (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (synWa (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
        (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)))
      x p0003
  have p0005 :=
    @gN1926 (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)) x
  have p0006 :=
    @gN3bitrri (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) (synCin B C))))
      (.all x (.imp (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) (.classMem (.cv x) C))))
      (.all x (synWa (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
          (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))))
      (synWa (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))))
      p0002 p0004 p0005
  have p0007 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @gDfss2 x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0009 :=
    @gAnbi12i (synWss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWss A C) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))) p0007
      p0008
  have p0010 :=
    @gDfss2 x A (synCin B C)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
  have p0011 :=
    @gN3bitr4i
      (synWa (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) (synCin B C))))
      (synWa (synWss A B) (synWss A C)) (synWss A (synCin B C)) p0006 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_ssini`. -/
@[expose]
noncomputable def gSsini (A : Class) (B : Class) (C : Class)
    (hyp_ssini_1 : Nominal.NPrf (synWss A B))
    (hyp_ssini_2 : Nominal.NPrf (synWss A C)) : Nominal.NPrf (synWss A (synCin B C)) :=
  by
  have p0000 := @gPm32i (synWss A B) (synWss A C) hyp_ssini_1 hyp_ssini_2
  have p0001 := @gSsin A B C
  have p0002 :=
    @gMpbi (synWa (synWss A B) (synWss A C)) (synWss A (synCin B C)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ssrin`. -/
@[expose]
noncomputable def gSsrin (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCin A C) (synCin B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gSsel A B (.cv x)
  have p0001 :=
    @gAnim1d (synWss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 := @gElin (.cv x) A C
  have p0003 := @gElin (.cv x) B C
  have p0004 :=
    @gN3imtr4g (synWss A B) (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.classMem (.cv x) (synCin A C)) (.classMem (.cv x) (synCin B C)) p0001 p0002
      p0003
  have p0005 :=
    @gSsrdv (synWss A B) x (synCin A C) (synCin B C)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_sslin`. -/
@[expose]
noncomputable def gSslin (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCin C A) (synCin C B))) :=
  by
  have p0000 := @gSsrin A B C
  have p0001 := @gIncom C A
  have p0002 := @gIncom C B
  have p0003 :=
    @gN3sstr4g (synWss A B) (synCin A C) (synCin B C) (synCin C A) (synCin C B)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_dfss4`. -/
@[expose]
noncomputable def gDfss4 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (.classEq (synCdif B (synCdif B A)) A)) :=
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
  have p0000 := @gSseqin2 A B
  have p0001 := @gEldif (.cv x) B A
  have p0002 :=
    @gNotbii (.classMem (.cv x) (synCdif B A))
      (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A))) p0001
  have p0003 :=
    @gAnbi2i (.neg (.classMem (.cv x) (synCdif B A)))
      (.neg (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A))))
      (.classMem (.cv x) B) p0002
  have p0004 := @gElin (.cv x) B A
  have p0005 := @gAbai (.classMem (.cv x) B) (.classMem (.cv x) A)
  have p0006 := @gIman (.classMem (.cv x) B) (.classMem (.cv x) A)
  have p0007 :=
    @gAnbi2i (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.neg (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A))))
      (.classMem (.cv x) B) p0006
  have p0008 :=
    @gN3bitri (.classMem (.cv x) (synCin B A))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) A))
      (synWa (.classMem (.cv x) B) (.imp (.classMem (.cv x) B) (.classMem (.cv x) A)))
      (synWa (.classMem (.cv x) B)
        (.neg (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A)))))
      p0004 p0005 p0007
  have p0009 :=
    @gBitr4i (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) (synCdif B A))))
      (synWa (.classMem (.cv x) B)
        (.neg (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A)))))
      (.classMem (.cv x) (synCin B A)) p0003 p0008
  have p0010 :=
    @gDifeqri x B (synCdif B A) (synCin B A)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      p0009
  have p0011 := @gEqeq1i (synCdif B (synCdif B A)) (synCin B A) A p0010
  have p0012 :=
    @gBitr4i (synWss A B) (.classEq (synCin B A) A)
      (.classEq (synCdif B (synCdif B A)) A) p0000 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_dfun2`. -/
@[expose]
noncomputable def gDfun2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCun A B) (synCdif (synCvv) (synCdif (synCdif (synCvv) A) B))) :=
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
  have p0000 := @gVex x
  have p0001 := @gEldif (.cv x) (synCvv) A
  have p0002 :=
    @gMpbiran (.classMem (.cv x) (synCdif (synCvv) A)) (.classMem (.cv x) (synCvv))
      (.neg (.classMem (.cv x) A)) p0000 p0001
  have p0003 :=
    @gAnbi1i (.classMem (.cv x) (synCdif (synCvv) A)) (.neg (.classMem (.cv x) A))
      (.neg (.classMem (.cv x) B)) p0002
  have p0004 := @gEldif (.cv x) (synCdif (synCvv) A) B
  have p0005 := @gIoran (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0006 :=
    @gN3bitr4i
      (synWa (.classMem (.cv x) (synCdif (synCvv) A)) (.neg (.classMem (.cv x) B)))
      (synWa (.neg (.classMem (.cv x) A)) (.neg (.classMem (.cv x) B)))
      (.classMem (.cv x) (synCdif (synCdif (synCvv) A) B))
      (.neg (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))) p0003 p0004 p0005
  have p0007 :=
    @gCon2bii (.classMem (.cv x) (synCdif (synCdif (synCvv) A) B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) p0006
  have p0008 := @gEldif (.cv x) (synCvv) (synCdif (synCdif (synCvv) A) B)
  have p0009 :=
    @gMpbiran
      (.classMem (.cv x) (synCdif (synCvv) (synCdif (synCdif (synCvv) A) B)))
      (.classMem (.cv x) (synCvv))
      (.neg (.classMem (.cv x) (synCdif (synCdif (synCvv) A) B))) p0000 p0008
  have p0010 :=
    @gBitr4i (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.neg (.classMem (.cv x) (synCdif (synCdif (synCvv) A) B)))
      (.classMem (.cv x) (synCdif (synCvv) (synCdif (synCdif (synCvv) A) B))) p0007
      p0009
  have p0011 :=
    @gUneqri x A B (synCdif (synCvv) (synCdif (synCdif (synCvv) A) B))
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
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_dfin2`. -/
@[expose]
noncomputable def gDfin2 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCin A B) (synCdif A (synCdif (synCvv) B))) :=
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
  have p0000 := @gVex x
  have p0001 := @gEldif (.cv x) (synCvv) B
  have p0002 :=
    @gMpbiran (.classMem (.cv x) (synCdif (synCvv) B)) (.classMem (.cv x) (synCvv))
      (.neg (.classMem (.cv x) B)) p0000 p0001
  have p0003 :=
    @gCon2bii (.classMem (.cv x) (synCdif (synCvv) B)) (.classMem (.cv x) B) p0002
  have p0004 :=
    @gAnbi2i (.classMem (.cv x) B) (.neg (.classMem (.cv x) (synCdif (synCvv) B)))
      (.classMem (.cv x) A) p0003
  have p0005 := @gEldif (.cv x) A (synCdif (synCvv) B)
  have p0006 :=
    @gBitr4i (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCdif (synCvv) B))))
      (.classMem (.cv x) (synCdif A (synCdif (synCvv) B))) p0004 p0005
  have p0007 :=
    @gIneqri x A B (synCdif A (synCdif (synCvv) B))
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
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_difin`. -/
@[expose]
noncomputable def gDifin (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCdif A (synCin A B)) (synCdif A B)) :=
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
  have p0000 := @gPm461 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @gAnclb (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0002 := @gElin (.cv x) A B
  have p0003 :=
    @gImbi2i (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) A) p0002
  have p0004 := @gIman (.classMem (.cv x) A) (.classMem (.cv x) (synCin A B))
  have p0005 :=
    @gN3bitr2i (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) (synCin A B)))
      (.neg (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCin A B))))) p0001
      p0003 p0004
  have p0006 :=
    @gCon2bii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCin A B)))) p0005
  have p0007 := @gEldif (.cv x) A B
  have p0008 :=
    @gN3bitr4i (.neg (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCin A B))))
      (.classMem (.cv x) (synCdif A B)) p0000 p0006 p0007
  have p0009 :=
    @gDifeqri x A (synCin A B) (synCdif A B)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_dfun3`. -/
@[expose]
noncomputable def gDfun3 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCun A B)
        (synCdif (synCvv) (synCin (synCdif (synCvv) A) (synCdif (synCvv) B)))) :=
  by
  have p0000 := @gDfun2 A B
  have p0001 := @gDfin2 (synCdif (synCvv) A) (synCdif (synCvv) B)
  have p0002 := @gDdif B
  have p0003 :=
    @gDifeq2i (synCdif (synCvv) (synCdif (synCvv) B)) B (synCdif (synCvv) A) p0002
  have p0004 :=
    @gEqtr2i (synCin (synCdif (synCvv) A) (synCdif (synCvv) B))
      (synCdif (synCdif (synCvv) A) (synCdif (synCvv) (synCdif (synCvv) B)))
      (synCdif (synCdif (synCvv) A) B) p0001 p0003
  have p0005 :=
    @gDifeq2i (synCdif (synCdif (synCvv) A) B)
      (synCin (synCdif (synCvv) A) (synCdif (synCvv) B)) (synCvv) p0004
  have p0006 :=
    @gEqtri (synCun A B) (synCdif (synCvv) (synCdif (synCdif (synCvv) A) B))
      (synCdif (synCvv) (synCin (synCdif (synCvv) A) (synCdif (synCvv) B))) p0000
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_dfin4`. -/
@[expose]
noncomputable def gDfin4 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCin A B) (synCdif A (synCdif A B))) :=
  by
  have p0000 := @gInss1 A B
  have p0001 := @gDfss4 (synCin A B) A
  have p0002 :=
    @gMpbi (synWss (synCin A B) A)
      (.classEq (synCdif A (synCdif A (synCin A B))) (synCin A B)) p0000 p0001
  have p0003 := @gDifin A B
  have p0004 := @gDifeq2i (synCdif A (synCin A B)) (synCdif A B) A p0003
  have p0005 :=
    @gEqtr3i (synCdif A (synCdif A (synCin A B))) (synCin A B)
      (synCdif A (synCdif A B)) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_invdif`. -/
@[expose]
noncomputable def gInvdif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCin A (synCdif (synCvv) B)) (synCdif A B)) :=
  by
  have p0000 := @gDfin2 A (synCdif (synCvv) B)
  have p0001 := @gDdif B
  have p0002 := @gDifeq2i (synCdif (synCvv) (synCdif (synCvv) B)) B A p0001
  have p0003 :=
    @gEqtri (synCin A (synCdif (synCvv) B))
      (synCdif A (synCdif (synCvv) (synCdif (synCvv) B))) (synCdif A B) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_indi`. -/
@[expose]
noncomputable def gIndi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCin A (synCun B C)) (synCun (synCin A B) (synCin A C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gAndi (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0001 := @gElin (.cv x) A B
  have p0002 := @gElin (.cv x) A C
  have p0003 :=
    @gOrbi12i (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classMem (.cv x) (synCin A C))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) C)) p0001 p0002
  have p0004 :=
    @gBitr4i
      (synWa (.classMem (.cv x) A) (synWo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (synWo (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
        (synWa (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (synWo (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) (synCin A C))) p0000
      p0003
  have p0005 := @gElun (.cv x) B C
  have p0006 :=
    @gAnbi2i (.classMem (.cv x) (synCun B C))
      (synWo (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0005
  have p0007 := @gElun (.cv x) (synCin A B) (synCin A C)
  have p0008 :=
    @gN3bitr4i
      (synWa (.classMem (.cv x) A) (synWo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (synWo (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) (synCin A C)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) (synCun B C)))
      (.classMem (.cv x) (synCun (synCin A B) (synCin A C))) p0004 p0006 p0007
  have p0009 :=
    @gIneqri x A (synCun B C) (synCun (synCin A B) (synCin A C))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_undi`. -/
@[expose]
noncomputable def gUndi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCun A (synCin B C)) (synCin (synCun A B) (synCun A C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gElin (.cv x) B C
  have p0001 :=
    @gOrbi2i (.classMem (.cv x) (synCin B C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0000
  have p0002 := @gOrdi (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0003 := @gElin (.cv x) (synCun A B) (synCun A C)
  have p0004 := @gElun (.cv x) A B
  have p0005 := @gElun (.cv x) A C
  have p0006 :=
    @gAnbi12i (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classMem (.cv x) (synCun A C))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) C)) p0004 p0005
  have p0007 :=
    @gBitr2i (.classMem (.cv x) (synCin (synCun A B) (synCun A C)))
      (synWa (.classMem (.cv x) (synCun A B)) (.classMem (.cv x) (synCun A C)))
      (synWa (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
        (synWo (.classMem (.cv x) A) (.classMem (.cv x) C)))
      p0003 p0006
  have p0008 :=
    @gN3bitri (synWo (.classMem (.cv x) A) (.classMem (.cv x) (synCin B C)))
      (synWo (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (synWa (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
        (synWo (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (.classMem (.cv x) (synCin (synCun A B) (synCun A C))) p0001 p0002 p0007
  have p0009 :=
    @gUneqri x A (synCin B C) (synCin (synCun A B) (synCun A C))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_indir`. -/
@[expose]
noncomputable def gIndir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCin (synCun A B) C) (synCun (synCin A C) (synCin B C))) :=
  by
  have p0000 := @gIndi C A B
  have p0001 := @gIncom (synCun A B) C
  have p0002 := @gIncom A C
  have p0003 := @gIncom B C
  have p0004 :=
    @gUneq12i (synCin A C) (synCin C A) (synCin B C) (synCin C B) p0002 p0003
  have p0005 :=
    @gN3eqtr4i (synCin C (synCun A B)) (synCun (synCin C A) (synCin C B))
      (synCin (synCun A B) C) (synCun (synCin A C) (synCin B C)) p0000 p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_undir`. -/
@[expose]
noncomputable def gUndir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCun (synCin A B) C) (synCin (synCun A C) (synCun B C))) :=
  by
  have p0000 := @gUndi C A B
  have p0001 := @gUncom (synCin A B) C
  have p0002 := @gUncom A C
  have p0003 := @gUncom B C
  have p0004 :=
    @gIneq12i (synCun A C) (synCun C A) (synCun B C) (synCun C B) p0002 p0003
  have p0005 :=
    @gN3eqtr4i (synCun C (synCin A B)) (synCin (synCun C A) (synCun C B))
      (synCun (synCin A B) C) (synCin (synCun A C) (synCun B C)) p0000 p0001 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay
