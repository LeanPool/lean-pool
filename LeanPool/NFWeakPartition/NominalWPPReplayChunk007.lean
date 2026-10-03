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

@[expose]
noncomputable def g_rspcimedv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_x : x ∉ ph.fv) (hyp_rspcimdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_rspcimedv_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (.imp ch ps))) :
    Nominal.NPrf (.imp ph (.imp ch (syn_wrex x B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_con3d (syn_wa ph (.classEq (.cv x) A)) ch ps hyp_rspcimedv_2
  have p0001 :=
    @g_rspcimdv ph (.neg ps) (.neg ch) x A B
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
  have p0002 := @g_con2d ph (syn_wral x B (.neg ps)) ch p0001
  have p0003 := @g_dfrex2 ps x B
  have p0004 :=
    @g_syl6ibr ph ch (.neg (syn_wral x B (.neg ps))) (syn_wrex x B ps) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_rspcdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_x : x ∉ ph.fv) (hyp_rspcdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_rspcdv_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wral x B ps) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_biimpd (syn_wa ph (.classEq (.cv x) A)) ps ch hyp_rspcdv_2
  have p0001 :=
    @g_rspcimdv ph ps ch x A B
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

@[expose]
noncomputable def g_rspcedv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ph_x : x ∉ ph.fv) (hyp_rspcdv_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_rspcdv_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.imp ch (syn_wrex x B ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_biimprd (syn_wa ph (.classEq (.cv x) A)) ps ch hyp_rspcdv_2
  have p0001 :=
    @g_rspcimedv ph ps ch x A B
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

@[expose]
noncomputable def g_rspc2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv)
    (dv_x_y : x ≠ y) (hyp_rspc2_1 : Nominal.NPrf (syn_wnf x ch))
    (hyp_rspc2_2 : Nominal.NPrf (syn_wnf y ps))
    (hyp_rspc2_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ch)))
    (hyp_rspc2_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ch ps))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D))
        (.imp (syn_wral x C (syn_wral y D ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @g_nfcv x D
      (by
        first
        | (aesop))
  have p0001 := @g_nfral ch x y D p0000 hyp_rspc2_1
  have p0002 :=
    @g_ralbidv (.classEq (.cv x) A) ph ch y D
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
    @g_rspc (syn_wral y D ph) (syn_wral y D ch) x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0001 p0002
  have p0004 :=
    @g_rspc ch ps y B D
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_rspc2_2 hyp_rspc2_4
  have p0005 :=
    @g_sylan9 (.classMem A C) (syn_wral x C (syn_wral y D ph)) (syn_wral y D ch)
      (.classMem B D) ps p0003 p0004
  exact p0005

@[expose]
noncomputable def g_rspc2v (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_rspc2v_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ch)))
    (hyp_rspc2v_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ch ps))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D))
        (.imp (syn_wral x C (syn_wral y D ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @g_nfv ch x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_rspc2 ph ps ch x y A B C D
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

@[expose]
noncomputable def g_rspc2va (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_rspc2v_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ch)))
    (hyp_rspc2v_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ch ps))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem A C) (.classMem B D)) (syn_wral x C (syn_wral y D ph)))
        ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @g_rspc2v ph ps ch x y A B C D
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
    @g_imp (syn_wa (.classMem A C) (.classMem B D)) (syn_wral x C (syn_wral y D ph)) ps
      p0000
  exact p0001

@[expose]
noncomputable def g_rspc2ev (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_rspc2v_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ch)))
    (hyp_rspc2v_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ch ps))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A C) (.classMem B D) ps) (syn_wrex x C (syn_wrex y D ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  have p0000 :=
    @g_rspcev ch ps y B D
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
    @g_anim2i (syn_wa (.classMem B D) ps) (syn_wrex y D ch) (.classMem A C) p0000
  have p0002 :=
    @g_n_3impb (.classMem A C) (.classMem B D) ps
      (syn_wa (.classMem A C) (syn_wrex y D ch)) p0001
  have p0003 :=
    @g_rexbidv (.classEq (.cv x) A) ph ch y D
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
    @g_rspcev (syn_wrex y D ph) (syn_wrex y D ch) x A C
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
    @g_syl (syn_w3a (.classMem A C) (.classMem B D) ps)
      (syn_wa (.classMem A C) (syn_wrex y D ch)) (syn_wrex x C (syn_wrex y D ph)) p0002
      p0004
  exact p0005

@[expose]
noncomputable def g_rspc3v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) (T : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_y : y ∉ B.fv)
    (dv_B_z : z ∉ B.fv) (dv_C_z : z ∉ C.fv) (dv_R_x : x ∉ R.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_T_x : x ∉ T.fv) (dv_T_y : y ∉ T.fv) (dv_T_z : z ∉ T.fv)
    (dv_ch_x : x ∉ ch.fv) (dv_ps_z : z ∉ ps.fv) (dv_th_y : y ∉ th.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_rspc3v_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ch)))
    (hyp_rspc3v_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ch th)))
    (hyp_rspc3v_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (syn_wb th ps))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A R) (.classMem B S) (.classMem C T))
        (.imp (syn_wral x R (syn_wral y S (syn_wral z T ph))) ps)) :=
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
    @g_ralbidv (.classEq (.cv x) A) ph ch z T
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
    @g_ralbidv (.classEq (.cv y) B) ch th z T
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
    @g_rspc2v (syn_wral z T ph) (syn_wral z T th) (syn_wral z T ch) x y A B R S
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
    @g_rspcv th ps z C T
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
    @g_sylan9 (syn_wa (.classMem A R) (.classMem B S))
      (syn_wral x R (syn_wral y S (syn_wral z T ph))) (syn_wral z T th) (.classMem C T) ps
      p0002 p0003
  have p0005 :=
    @g_n_3impa (.classMem A R) (.classMem B S) (.classMem C T)
      (.imp (syn_wral x R (syn_wral y S (syn_wral z T ph))) ps) p0004
  exact p0005

@[expose]
noncomputable def g_eqvinc (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_eqvinc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (syn_wex x (syn_wa (.classEq (.cv x) A) (.classEq (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_isseti x A
      (by
        first
        | (aesop))
      hyp_eqvinc_1
  have p0001 := Nominal.ax1 (.classEq (.cv x) A) (.classEq A B)
  have p0002 := @g_eqtr (.cv x) A B
  have p0003 := @g_ex (.classEq (.cv x) A) (.classEq A B) (.classEq (.cv x) B) p0002
  have p0004 :=
    @g_jca (.classEq (.cv x) A) (.imp (.classEq A B) (.classEq (.cv x) A))
      (.imp (.classEq A B) (.classEq (.cv x) B)) p0001 p0003
  have p0005 :=
    @g_eximi (.classEq (.cv x) A)
      (syn_wa (.imp (.classEq A B) (.classEq (.cv x) A))
        (.imp (.classEq A B) (.classEq (.cv x) B)))
      x p0004
  have p0006 := @g_pm3_43 (.classEq A B) (.classEq (.cv x) A) (.classEq (.cv x) B)
  have p0007 :=
    @g_eximi
      (syn_wa (.imp (.classEq A B) (.classEq (.cv x) A))
        (.imp (.classEq A B) (.classEq (.cv x) B)))
      (.imp (.classEq A B) (syn_wa (.classEq (.cv x) A) (.classEq (.cv x) B))) x p0006
  have p0008 :=
    @g_mp2b (syn_wex x (.classEq (.cv x) A))
      (syn_wex x (syn_wa (.imp (.classEq A B) (.classEq (.cv x) A))
          (.imp (.classEq A B) (.classEq (.cv x) B))))
      (syn_wex x (.imp (.classEq A B) (syn_wa (.classEq (.cv x) A) (.classEq (.cv x) B))))
      p0000 p0005 p0007
  have p0009 :=
    @g_n_19_37aiv (.classEq A B) (syn_wa (.classEq (.cv x) A) (.classEq (.cv x) B)) x
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
  have p0010 := @g_eqtr2 (.cv x) A B
  have p0011 :=
    @g_exlimiv (syn_wa (.classEq (.cv x) A) (.classEq (.cv x) B)) (.classEq A B) x
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
    @g_impbii (.classEq A B)
      (syn_wex x (syn_wa (.classEq (.cv x) A) (.classEq (.cv x) B))) p0009 p0011
  exact p0012

@[expose]
noncomputable def g_alexeq (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_alexeq_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.all x (.imp (.classEq (.cv x) A) ph))
        (syn_wex x (syn_wa (.classEq (.cv x) A) ph))) :=
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
  have p0000 := @g_eqeq2 (.cv y) A (.cv x)
  have p0001 :=
    @g_anbi1d (.classEq (.cv y) A) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) A) ph
      p0000
  have p0002 :=
    @g_exbidv (.classEq (.cv y) A) (syn_wa (.classEq (.cv x) (.cv y)) ph)
      (syn_wa (.classEq (.cv x) A) ph) x
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
    @g_imbi1d (.classEq (.cv y) A) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) A) ph
      p0000
  have p0004 :=
    @g_albidv (.classEq (.cv y) A) (.imp (.classEq (.cv x) (.cv y)) ph)
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
    @g_sb56 ph x y
      (by
        first
        | (aesop))
  have p0006_e03_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) ph))
        (.all x (.imp (.classEq (.cv x) (.cv y)) ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
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
    @g_vtoclb (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) ph))
      (.all x (.imp (.classEq (.cv x) (.cv y)) ph))
      (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) (.all x (.imp (.classEq (.cv x) A) ph))
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
    @g_bicomi (syn_wex x (syn_wa (.classEq (.cv x) A) ph))
      (.all x (.imp (.classEq (.cv x) A) ph)) p0006
  exact p0007

@[expose]
noncomputable def g_ceqex (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classEq (.cv x) A) (syn_wb ph (syn_wex x (syn_wa (.classEq (.cv x) A) ph)))) :=
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
  have p0000 := @g_n_19_8a (.classEq (.cv x) A) x
  have p0001 :=
    @g_isset x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sylibr (.classEq (.cv x) A) (syn_wex x (.classEq (.cv x) A))
      (.classMem A (syn_cvv)) p0000 p0001
  have p0003 := @g_eqeq2 (.cv y) A (.cv x)
  have p0004 :=
    @g_anbi1d (.classEq (.cv y) A) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) A) ph
      p0003
  have p0005 :=
    @g_exbidv (.classEq (.cv y) A) (syn_wa (.classEq (.cv x) (.cv y)) ph)
      (syn_wa (.classEq (.cv x) A) ph) x
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
    @g_bibi2d (.classEq (.cv y) A) (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) ph))
      (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ph p0005
  have p0007 :=
    @g_imbi12d (.classEq (.cv y) A) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) A)
      (syn_wb ph (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) ph)))
      (syn_wb ph (syn_wex x (syn_wa (.classEq (.cv x) A) ph))) p0003 p0006
  have p0008 := @g_n_19_8a (syn_wa (.classEq (.cv x) (.cv y)) ph) x
  have p0009 :=
    @g_ex (.classEq (.cv x) (.cv y)) ph (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) ph))
      p0008
  have p0010 := @g_vex y
  have p0011 :=
    @g_alexeq ph x (.cv y)
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
  have p0012 := @g_sp (.imp (.classEq (.cv x) (.cv y)) ph) x
  have p0013 :=
    @g_com12 (.all x (.imp (.classEq (.cv x) (.cv y)) ph)) (.classEq (.cv x) (.cv y)) ph
      p0012
  have p0014 :=
    @g_syl5bir (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) ph))
      (.all x (.imp (.classEq (.cv x) (.cv y)) ph)) (.classEq (.cv x) (.cv y)) ph p0011
      p0013
  have p0015 :=
    @g_impbid (.classEq (.cv x) (.cv y)) ph
      (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) ph)) p0009 p0014
  have p0016 :=
    @g_vtoclg
      (.imp (.classEq (.cv x) (.cv y))
        (syn_wb ph (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) ph))))
      (.imp (.classEq (.cv x) A) (syn_wb ph (syn_wex x (syn_wa (.classEq (.cv x) A) ph))))
      y A (syn_cvv)
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
    @g_mpcom (.classMem A (syn_cvv)) (.classEq (.cv x) A)
      (syn_wb ph (syn_wex x (syn_wa (.classEq (.cv x) A) ph))) p0002 p0016
  exact p0017

@[expose]
noncomputable def g_ceqsexg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (hyp_ceqsexg_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_ceqsexg_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 := @g_nfe1 (syn_wa (.classEq (.cv x) A) ph) x
  have p0002 :=
    @g_nfbi (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps x p0001 hyp_ceqsexg_1
  have p0003 :=
    @g_ceqex ph x A
      (by
        first
        | (aesop))
  have p0004 :=
    @g_bibi12d (.classEq (.cv x) A) ph (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ph ps
      p0003 hyp_ceqsexg_2
  have p0005 := @g_biid ph
  have p0006 :=
    @g_vtoclgf (syn_wb ph ph) (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps) x A
      V p0000 p0002 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_ceqsexgv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsexgv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_ceqsexg ph ps x A V
      (by
        first
        | (aesop))
      p0000 hyp_ceqsexgv_1
  exact p0001

@[expose]
noncomputable def g_ceqsrexv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsrexv_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (.classMem A B) (syn_wb (syn_wrex x B (syn_wa (.classEq (.cv x) A) ph)) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := (Nominal.biimpRefl (syn_wrex x B (syn_wa (.classEq (.cv x) A) ph)))
  have p0001 := @g_an12 (.classEq (.cv x) A) (.classMem (.cv x) B) ph
  have p0002 :=
    @g_exbii (syn_wa (.classEq (.cv x) A) (syn_wa (.classMem (.cv x) B) ph))
      (syn_wa (.classMem (.cv x) B) (syn_wa (.classEq (.cv x) A) ph)) x p0001
  have p0003 :=
    @g_bitr4i (syn_wrex x B (syn_wa (.classEq (.cv x) A) ph))
      (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wa (.classEq (.cv x) A) ph)))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wa (.classMem (.cv x) B) ph))) p0000
      p0002
  have p0004 := @g_eleq1 (.cv x) A B
  have p0005 :=
    @g_anbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0004
      hyp_ceqsrexv_1
  have p0006 :=
    @g_ceqsexgv (syn_wa (.classMem (.cv x) B) ph) (syn_wa (.classMem A B) ps) x A B
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
    @g_bianabs (.classMem A B)
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wa (.classMem (.cv x) B) ph))) ps p0006
  have p0008 :=
    @g_syl5bb (syn_wrex x B (syn_wa (.classEq (.cv x) A) ph))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wa (.classMem (.cv x) B) ph)))
      (.classMem A B) ps p0003 p0007
  exact p0008

@[expose]
noncomputable def g_clel2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_clel2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem A B) (.all x (.imp (.classEq (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_eleq1 (.cv x) A B
  have p0001 :=
    @g_ceqsalv (.classMem (.cv x) B) (.classMem A B) x A
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
    @g_bicomi (.all x (.imp (.classEq (.cv x) A) (.classMem (.cv x) B))) (.classMem A B)
      p0001
  exact p0002

@[expose]
noncomputable def g_clel3g (x : Var) (A : Class) (B : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem B V) (syn_wb (.classMem A B)
          (syn_wex x (syn_wa (.classEq (.cv x) B) (.classMem A (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  have p0000 := @g_eleq2 (.cv x) B A
  have p0001 :=
    @g_ceqsexgv (.classMem A (.cv x)) (.classMem A B) x B V
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
    @g_bicomd (.classMem B V)
      (syn_wex x (syn_wa (.classEq (.cv x) B) (.classMem A (.cv x)))) (.classMem A B)
      p0001
  exact p0002

@[expose]
noncomputable def g_clel3 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_clel3_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem A B)
        (syn_wex x (syn_wa (.classEq (.cv x) B) (.classMem A (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_clel3g x A B (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := Nominal.mp hyp_clel3_1 p0000
  exact p0001

@[expose]
noncomputable def g_elabgf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_elabgf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_elabgf_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_elabgf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A B) (syn_wb (.classMem A (.cab x ph)) ps)) :=
  by
  have p0000 := @g_nfab1 ph x
  have p0001 := @g_nfel x A (.cab x ph) hyp_elabgf_1 p0000
  have p0002 := @g_nfbi (.classMem A (.cab x ph)) ps x p0001 hyp_elabgf_2
  have p0003 := @g_eleq1 (.cv x) A (.cab x ph)
  have p0004 :=
    @g_bibi12d (.classEq (.cv x) A) (.classMem (.cv x) (.cab x ph))
      (.classMem A (.cab x ph)) ph ps p0003 hyp_elabgf_3
  have p0005 := @g_abid ph x
  have p0006 :=
    @g_vtoclgf (syn_wb (.classMem (.cv x) (.cab x ph)) ph)
      (syn_wb (.classMem A (.cab x ph)) ps) x A B hyp_elabgf_1 p0002 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_elabf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_elabf_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_elabf_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_elabf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.classMem A (.cab x ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 := @g_elabgf ph ps x A (syn_cvv) p0000 hyp_elabf_1 hyp_elabf_3
  have p0002 := Nominal.mp hyp_elabf_2 p0001
  exact p0002

@[expose]
noncomputable def g_elab (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_elab_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_elab_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.classMem A (.cab x ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_elabf ph ps x A
      (by
        first
        | (aesop))
      p0000 hyp_elab_1 hyp_elab_2
  exact p0001

@[expose]
noncomputable def g_elabg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem A (.cab x ph)) ps)) :=
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
  have p0002 := @g_elabgf ph ps x A V p0000 p0001 hyp_elabg_1
  exact p0002

@[expose]
noncomputable def g_elab2g (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (V : Class) (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elab2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_elab2g_2 : Nominal.NPrf (.classEq B (.cab x ph))) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem A B) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  have p0000 := @g_eleq2i B (.cab x ph) A hyp_elab2g_2
  have p0001 :=
    @g_elabg ph ps x A V
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_elab2g_1
  have p0002 :=
    @g_syl5bb (.classMem A B) (.classMem A (.cab x ph)) (.classMem A V) ps p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elab2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elab2_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_elab2_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_elab2_3 : Nominal.NPrf (.classEq B (.cab x ph))) :
    Nominal.NPrf (syn_wb (.classMem A B) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_elab2g ph ps x A B (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_elab2_2 hyp_elab2_3
  have p0001 := Nominal.mp hyp_elab2_1 p0000
  exact p0001

@[expose]
noncomputable def g_elab3gf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_elab3gf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_elab3gf_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_elab3gf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.imp ps (.classMem A B)) (syn_wb (.classMem A (.cab x ph)) ps)) :=
  by
  have p0000 := @g_elabgf ph ps x A (.cab x ph) hyp_elab3gf_1 hyp_elab3gf_2 hyp_elab3gf_3
  have p0001 := @g_ibi (.classMem A (.cab x ph)) ps p0000
  have p0002 := @g_pm2_21 ps (.classMem A (.cab x ph))
  have p0003 := @g_impbid2 (.neg ps) (.classMem A (.cab x ph)) ps p0001 p0002
  have p0004 := @g_elabgf ph ps x A B hyp_elab3gf_1 hyp_elab3gf_2 hyp_elab3gf_3
  have p0005 := @g_ja ps (.classMem A B) (syn_wb (.classMem A (.cab x ph)) ps) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_elab3g (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elab3g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.imp ps (.classMem A B)) (syn_wb (.classMem A (.cab x ph)) ps)) :=
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
  have p0002 := @g_elab3gf ph ps x A B p0000 p0001 hyp_elab3g_1
  exact p0002

@[expose]
noncomputable def g_elab3 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_elab3_1 : Nominal.NPrf (.imp ps (.classMem A (syn_cvv))))
    (hyp_elab3_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.classMem A (.cab x ph)) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_elab3g ph ps x A (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_elab3_2
  have p0001 := Nominal.mp hyp_elab3_1 p0000
  exact p0001

@[expose]
noncomputable def g_elrabf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_elrabf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_elrabf_2 : Nominal.NPrf (syn_wnfc x B))
    (hyp_elrabf_3 : Nominal.NPrf (syn_wnf x ps))
    (hyp_elrabf_4 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_crab x B ph)) (syn_wa (.classMem A B) ps)) :=
  by
  have p0000 := @g_elex A (syn_crab x B ph)
  have p0001 := @g_elex A B
  have p0002 := @g_adantr (.classMem A B) (.classMem A (syn_cvv)) ps p0001
  have p0003 := (Nominal.classEqRefl (syn_crab x B ph))
  have p0004 :=
    @g_eleq2i (syn_crab x B ph) (.cab x (syn_wa (.classMem (.cv x) B) ph)) A p0003
  have p0005 := @g_nfel x A B hyp_elrabf_1 hyp_elrabf_2
  have p0006 := @g_nfan (.classMem A B) ps x p0005 hyp_elrabf_3
  have p0007 := @g_eleq1 (.cv x) A B
  have p0008 :=
    @g_anbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) ph ps p0007
      hyp_elrabf_4
  have p0009 :=
    @g_elabgf (syn_wa (.classMem (.cv x) B) ph) (syn_wa (.classMem A B) ps) x A (syn_cvv)
      hyp_elrabf_1 p0006 p0008
  have p0010 :=
    @g_syl5bb (.classMem A (syn_crab x B ph))
      (.classMem A (.cab x (syn_wa (.classMem (.cv x) B) ph))) (.classMem A (syn_cvv))
      (syn_wa (.classMem A B) ps) p0004 p0009
  have p0011 :=
    @g_pm5_21nii (.classMem A (syn_crab x B ph)) (.classMem A (syn_cvv))
      (syn_wa (.classMem A B) ps) p0000 p0002 p0010
  exact p0011

@[expose]
noncomputable def g_elrab (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elrab_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_crab x B ph)) (syn_wa (.classMem A B) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
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
  have p0002 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0003 := @g_elrabf ph ps x A B p0000 p0001 p0002 hyp_elrab_1
  exact p0003

@[expose]
noncomputable def g_elrab2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elrab2_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_elrab2_2 : Nominal.NPrf (.classEq C (syn_crab x B ph))) :
    Nominal.NPrf (syn_wb (.classMem A C) (syn_wa (.classMem A B) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @g_eleq2i C (syn_crab x B ph) A hyp_elrab2_2
  have p0001 :=
    @g_elrab ph ps x A B
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
    @g_bitri (.classMem A C) (.classMem A (syn_crab x B ph)) (syn_wa (.classMem A B) ps)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ralab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralab_1 : Nominal.NPrf (.imp (.objEq y x) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wral x (.cab y ph) ch) (.all x (.imp ps ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := (Nominal.biimpRefl (syn_wral x (.cab y ph) ch))
  have p0001 := @g_vex x
  have p0002_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (syn_wb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_ralab_1
  have p0002 :=
    @g_elab ph ps y (.cv x)
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
  have p0003 := @g_imbi1i (.classMem (.cv x) (.cab y ph)) ps ch p0002
  have p0004 := @g_albii (.imp (.classMem (.cv x) (.cab y ph)) ch) (.imp ps ch) x p0003
  have p0005 :=
    @g_bitri (syn_wral x (.cab y ph) ch)
      (.all x (.imp (.classMem (.cv x) (.cab y ph)) ch)) (.all x (.imp ps ch)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_rexab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralab_1 : Nominal.NPrf (.imp (.objEq y x) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x (.cab y ph) ch) (syn_wex x (syn_wa ps ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := (Nominal.biimpRefl (syn_wrex x (.cab y ph) ch))
  have p0001 := @g_vex x
  have p0002_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (syn_wb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_ralab_1
  have p0002 :=
    @g_elab ph ps y (.cv x)
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
  have p0003 := @g_anbi1i (.classMem (.cv x) (.cab y ph)) ps ch p0002
  have p0004 :=
    @g_exbii (syn_wa (.classMem (.cv x) (.cab y ph)) ch) (syn_wa ps ch) x p0003
  have p0005 :=
    @g_bitri (syn_wrex x (.cab y ph) ch)
      (syn_wex x (syn_wa (.classMem (.cv x) (.cab y ph)) ch)) (syn_wex x (syn_wa ps ch))
      p0000 p0004
  exact p0005

@[expose]
noncomputable def g_rexrab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (dv_A_y : y ∉ A.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralab_1 : Nominal.NPrf (.imp (.objEq y x) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_wrex x (syn_crab y A ph) ch) (syn_wrex x A (syn_wa ps ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (syn_wb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_ralab_1
  have p0000 :=
    @g_elrab ph ps y (.cv x) A
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
    @g_anbi1i (.classMem (.cv x) (syn_crab y A ph)) (syn_wa (.classMem (.cv x) A) ps) ch
      p0000
  have p0002 := @g_anass (.classMem (.cv x) A) ps ch
  have p0003 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_crab y A ph)) ch)
      (syn_wa (syn_wa (.classMem (.cv x) A) ps) ch)
      (syn_wa (.classMem (.cv x) A) (syn_wa ps ch)) p0001 p0002
  have p0004 := @g_rexbii2 ch (syn_wa ps ch) x (syn_crab y A ph) A p0003
  exact p0004

@[expose]
noncomputable def g_ralab2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_ralab2_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ps ch))) :
    Nominal.NPrf (syn_wb (syn_wral x (.cab y ph) ps) (.all y (.imp ph ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := (Nominal.biimpRefl (syn_wral x (.cab y ph) ps))
  have p0001 :=
    @g_nfsab1 ph y x
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfv ps y
      (by
        first
        | (aesop))
  have p0003 := @g_nfim (.classMem (.cv x) (.cab y ph)) ps y p0001 p0002
  have p0004 :=
    @g_nfv (.imp ph ch) x
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              Finset.mem_union] at ⊢;
            aesop))
  have p0005 := @g_eleq1 (.cv x) (.cv y) (.cab y ph)
  have p0006 := @g_abid ph y
  have p0007 :=
    @g_syl6bb (.classEq (.cv x) (.cv y)) (.classMem (.cv x) (.cab y ph))
      (.classMem (.cv y) (.cab y ph)) ph p0005 p0006
  have p0008_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb ps ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_ralab2_1
  have p0008 :=
    @g_imbi12d (.classEq (.cv x) (.cv y)) (.classMem (.cv x) (.cab y ph)) ph ps ch p0007
      p0008_e01_recanon
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (.imp (.classMem (.cv x) (.cab y ph)) ps) (.imp ph ch))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @g_cbval (.imp (.classMem (.cv x) (.cab y ph)) ps) (.imp ph ch) x y p0003 p0004
      p0009_e02_recanon
  have p0010 :=
    @g_bitri (syn_wral x (.cab y ph) ps)
      (.all x (.imp (.classMem (.cv x) (.cab y ph)) ps)) (.all y (.imp ph ch)) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_abidnf (x : Var) (z : Var) (A : Class) (dv_A_z : z ∉ A.fv)
    (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (syn_wnfc x A) (.classEq (.cab z (.all x (.classMem (.cv z) A))) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv
  have p0000 := @g_sp (.classMem (.cv z) A) x
  have p0001 :=
    @g_nfcr x z A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 := @g_nfrd (syn_wnfc x A) (.classMem (.cv z) A) x p0001
  have p0003 :=
    @g_impbid2 (syn_wnfc x A) (.all x (.classMem (.cv z) A)) (.classMem (.cv z) A) p0000
      p0002
  have p0004 :=
    @g_eqabcdv (syn_wnfc x A) (.all x (.classMem (.cv z) A)) z A
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

@[expose]
noncomputable def g_eueq (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cvv)) (syn_weu x (.classEq (.cv x) A))) :=
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
  have p0000 := @g_eqtr3 (.cv x) (.cv y) A
  have p0001 :=
    @g_gen2
      (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) A)) (.classEq (.cv x) (.cv y)))
      x y p0000
  have p0002 :=
    @g_biantru
      (.all x (.all y (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) A))
            (.classEq (.cv x) (.cv y)))))
      (syn_wex x (.classEq (.cv x) A)) p0001
  have p0003 :=
    @g_isset x A
      (by
        first
        | (aesop))
  have p0004 := @g_eqeq1 (.cv x) (.cv y) A
  have p0005_e00_recanon :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (.classEq (.cv x) A) (.classEq (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_eu4 (.classEq (.cv x) A) (.classEq (.cv y) A) x y
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
      (syn_wb (syn_weu x (.classEq (.cv x) A)) (syn_wa (syn_wex x (.classEq (.cv x) A)) (.all x
            (.all y (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) A))
                (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wa
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
    @g_n_3bitr4i (syn_wex x (.classEq (.cv x) A))
      (syn_wa (syn_wex x (.classEq (.cv x) A)) (.all x (.all y
            (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) A))
              (.classEq (.cv x) (.cv y))))))
      (.classMem A (syn_cvv)) (syn_weu x (.classEq (.cv x) A)) p0002 p0003
      p0006_e02_recanon
  exact p0006

@[expose]
noncomputable def g_eueq1 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_eueq1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_weu x (.classEq (.cv x) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_eueq x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mpbi (.classMem A (syn_cvv)) (syn_weu x (.classEq (.cv x) A)) hyp_eueq1_1 p0000
  exact p0001

@[expose]
noncomputable def g_moeq (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wmo x (.classEq (.cv x) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_isset x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_eueq x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_bitr3i (syn_wex x (.classEq (.cv x) A)) (.classMem A (syn_cvv))
      (syn_weu x (.classEq (.cv x) A)) p0000 p0001
  have p0003 :=
    @g_biimpi (syn_wex x (.classEq (.cv x) A)) (syn_weu x (.classEq (.cv x) A)) p0002
  have p0004 := (Nominal.biimpRefl (syn_wmo x (.classEq (.cv x) A)))
  have p0005 :=
    @g_mpbir (syn_wmo x (.classEq (.cv x) A))
      (.imp (syn_wex x (.classEq (.cv x) A)) (syn_weu x (.classEq (.cv x) A))) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_rmo4 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_x_y : x ≠ y) (hyp_rmo4_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_wrmo x A ph)
        (syn_wral x A (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.biimpRefl (syn_wrmo x A ph))
  have p0001 := @g_an4 (.classMem (.cv x) A) ph (.classMem (.cv y) A) ps
  have p0002 := @g_ancom (.classMem (.cv x) A) (.classMem (.cv y) A)
  have p0003 :=
    @g_anbi1i (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) A)) (syn_wa ph ps) p0002
  have p0004 :=
    @g_bitri (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) A) ps))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa ph ps))
      (syn_wa (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) A)) (syn_wa ph ps)) p0001
      p0003
  have p0005 :=
    @g_imbi1i (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) A) ps))
      (syn_wa (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) A)) (syn_wa ph ps))
      (.objEq x y) p0004
  have p0006 :=
    @g_impexp (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) A)) (syn_wa ph ps)
      (.objEq x y)
  have p0007 :=
    @g_impexp (.classMem (.cv y) A) (.classMem (.cv x) A)
      (.imp (syn_wa ph ps) (.objEq x y))
  have p0008 :=
    @g_n_3bitri
      (.imp (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) A) ps))
        (.objEq x y))
      (.imp (syn_wa (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) A)) (syn_wa ph ps))
        (.objEq x y))
      (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) A))
        (.imp (syn_wa ph ps) (.objEq x y)))
      (.imp (.classMem (.cv y) A)
        (.imp (.classMem (.cv x) A) (.imp (syn_wa ph ps) (.objEq x y))))
      p0005 p0006 p0007
  have p0009 :=
    @g_albii
      (.imp (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) A) ps))
        (.objEq x y))
      (.imp (.classMem (.cv y) A)
        (.imp (.classMem (.cv x) A) (.imp (syn_wa ph ps) (.objEq x y))))
      y p0008
  have p0010 :=
    (Nominal.biimpRefl
      (syn_wral y A (.imp (.classMem (.cv x) A) (.imp (syn_wa ph ps) (.objEq x y)))))
  have p0011 :=
    @g_r19_21v (.classMem (.cv x) A) (.imp (syn_wa ph ps) (.objEq x y)) y A
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
    @g_n_3bitr2i
      (.all y (.imp (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) A) ps))
          (.objEq x y)))
      (.all y (.imp (.classMem (.cv y) A)
          (.imp (.classMem (.cv x) A) (.imp (syn_wa ph ps) (.objEq x y)))))
      (syn_wral y A (.imp (.classMem (.cv x) A) (.imp (syn_wa ph ps) (.objEq x y))))
      (.imp (.classMem (.cv x) A) (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))) p0009
      p0010 p0011
  have p0013 :=
    @g_albii
      (.all y (.imp (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) A) ps))
          (.objEq x y)))
      (.imp (.classMem (.cv x) A) (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))) x
      p0012
  have p0014 := @g_eleq1 (.cv x) (.cv y) A
  have p0015_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (.classMem (.cv x) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0015 :=
    @g_anbi12d (.objEq x y) (.classMem (.cv x) A) (.classMem (.cv y) A) ph ps
      p0015_e00_recanon hyp_rmo4_1
  have p0016 :=
    @g_mo4 (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) A) ps) x y
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
    (Nominal.biimpRefl (syn_wral x A (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))))
  have p0018 :=
    @g_n_3bitr4i
      (.all x (.all y (.imp
            (syn_wa (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv y) A) ps))
            (.objEq x y))))
      (.all x (.imp (.classMem (.cv x) A) (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))))
      (syn_wmo x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wral x A (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))) p0013 p0016 p0017
  have p0019 :=
    @g_bitri (syn_wrmo x A ph) (syn_wmo x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wral x A (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))) p0000 p0018
  exact p0019

@[expose]
noncomputable def g_reu4 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_x_y : x ≠ y) (hyp_rmo4_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_wreu x A ph) (syn_wa (syn_wrex x A ph)
          (syn_wral x A (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 := @g_reu5 ph x A
  have p0001 :=
    @g_rmo4 ph ps x y A
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
    @g_anbi2i (syn_wrmo x A ph)
      (syn_wral x A (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))) (syn_wrex x A ph)
      p0001
  have p0003 :=
    @g_bitri (syn_wreu x A ph) (syn_wa (syn_wrex x A ph) (syn_wrmo x A ph))
      (syn_wa (syn_wrex x A ph)
        (syn_wral x A (syn_wral y A (.imp (syn_wa ph ps) (.objEq x y)))))
      p0000 p0002
  exact p0003

@[expose]
noncomputable def g_dfsbcq (ph : Wff) (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wsbc A x ph) (syn_wsbc B x ph))) :=
  by
  have p0000 := @g_eleq1 A B (.cab x ph)
  have p0001 := (Nominal.biimpRefl (syn_wsbc A x ph))
  have p0002 := (Nominal.biimpRefl (syn_wsbc B x ph))
  have p0003 :=
    @g_n_3bitr4g (.classEq A B) (.classMem A (.cab x ph)) (.classMem B (.cab x ph))
      (syn_wsbc A x ph) (syn_wsbc B x ph) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_dfsbcq2 (ph : Wff) (x : Var) (y : Var) (A : Class) :
    Nominal.NPrf
      (.imp (.classEq (.cv y) A) (syn_wb (syn_wsb y x ph) (syn_wsbc A x ph))) :=
  by
  have p0000 := @g_eleq1 (.cv y) A (.cab x ph)
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0002 := (Nominal.biimpRefl (syn_wsbc A x ph))
  have p0003 := @g_bicomi (syn_wsbc A x ph) (.classMem A (.cab x ph)) p0002
  have p0004 :=
    @g_n_3bitr3g (.classEq (.cv y) A) (.classMem (.cv y) (.cab x ph))
      (.classMem A (.cab x ph)) (syn_wsb y x ph) (syn_wsbc A x ph) p0000 p0001 p0003
  exact p0004

@[expose]
noncomputable def g_sbsbc (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wb (syn_wsb y x ph) (syn_wsbc (.cv y) x ph)) :=
  by
  have p0000 := @g_eqid (.cv y)
  have p0001 := @g_dfsbcq2 ph x y (.cv y)
  have p0002_e00_recanon : Nominal.NPrf (.objEq y y) :=
    Nominal.RecanonTransportDev.transport
      (by exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _) p0000
  have p0002_e01_recanon :
    Nominal.NPrf (.imp (.objEq y y) (syn_wb (syn_wsb y x ph) (syn_wsbc (.cv y) x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex syn_wsbc
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 := Nominal.mp p0002_e00_recanon p0002_e01_recanon
  exact p0002

@[expose]
noncomputable def g_sbcex (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wsbc A x ph) (.classMem A (syn_cvv))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wsbc A x ph))
  have p0001 := @g_elex A (.cab x ph)
  have p0002 :=
    @g_sylbi (syn_wsbc A x ph) (.classMem A (.cab x ph)) (.classMem A (syn_cvv)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_spsbc (ph : Wff) (x : Var) (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.imp (.all x ph) (syn_wsbc A x ph))) :=
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
  have p0000 := @g_stdpc4 ph x y
  have p0001 := @g_sbsbc ph x y
  have p0002 := @g_sylib (.all x ph) (syn_wsb y x ph) (syn_wsbc (.cv y) x ph) p0000 p0001
  have p0003 := @g_dfsbcq ph x (.cv y) A
  have p0004 :=
    @g_syl5ib (.all x ph) (syn_wsbc (.cv y) x ph) (.classEq (.cv y) A) (syn_wsbc A x ph)
      p0002 p0003
  have p0005 :=
    @g_vtocleg (.imp (.all x ph) (syn_wsbc A x ph)) y A V
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

@[expose]
noncomputable def g_nfsbc1d (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_nfsbc1d_2 : Nominal.NPrf (.imp ph (syn_wnfc x A))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wsbc A x ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wsbc A x ps))
  have p0001 := @g_nfab1 ps x
  have p0002 := @g_a1i (syn_wnfc x (.cab x ps)) ph p0001
  have p0003 := @g_nfeld ph x A (.cab x ps) hyp_nfsbc1d_2 p0002
  have p0004 := @g_nfxfrd (syn_wsbc A x ps) (.classMem A (.cab x ps)) ph x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfsbcd (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (hyp_nfsbcd_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfsbcd_2 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_nfsbcd_3 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wsbc A y ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wsbc A y ps))
  have p0001 := @g_nfabd ph ps x y hyp_nfsbcd_1 hyp_nfsbcd_3
  have p0002 := @g_nfeld ph x A (.cab y ps) hyp_nfsbcd_2 p0001
  have p0003 := @g_nfxfrd (syn_wsbc A y ps) (.classMem A (.cab y ps)) ph x p0000 p0002
  exact p0003

@[expose]
noncomputable def g_sbcco (ph : Wff) (x : Var) (y : Var) (A : Class)
    (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf (syn_wb (syn_wsbc A y (syn_wsbc (.cv y) x ph)) (syn_wsbc A x ph)) :=
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
  have p0000 := @g_sbcex (syn_wsbc (.cv y) x ph) y A
  have p0001 := @g_sbcex ph x A
  have p0002 := @g_dfsbcq (syn_wsbc (.cv y) x ph) y (.cv z) A
  have p0003 := @g_dfsbcq ph x (.cv z) A
  have p0004 := @g_sbsbc ph x y
  have p0005 := @g_sbbii (syn_wsb y x ph) (syn_wsbc (.cv y) x ph) y z p0004
  have p0006 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0007 := @g_sbco2 ph x z y p0006
  have p0008 := @g_sbsbc (syn_wsbc (.cv y) x ph) y z
  have p0009 :=
    @g_n_3bitr3ri (syn_wsb z y (syn_wsb y x ph)) (syn_wsb z y (syn_wsbc (.cv y) x ph))
      (syn_wsb z x ph) (syn_wsbc (.cv z) y (syn_wsbc (.cv y) x ph)) p0005 p0007 p0008
  have p0010 := @g_sbsbc ph x z
  have p0011 :=
    @g_bitri (syn_wsbc (.cv z) y (syn_wsbc (.cv y) x ph)) (syn_wsb z x ph)
      (syn_wsbc (.cv z) x ph) p0009 p0010
  have p0012 :=
    @g_vtoclbg (syn_wsbc (.cv z) y (syn_wsbc (.cv y) x ph)) (syn_wsbc (.cv z) x ph)
      (syn_wsbc A y (syn_wsbc (.cv y) x ph)) (syn_wsbc A x ph) z A (syn_cvv)
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
    @g_pm5_21nii (syn_wsbc A y (syn_wsbc (.cv y) x ph)) (.classMem A (syn_cvv))
      (syn_wsbc A x ph) p0000 p0001 p0012
  exact p0013

@[expose]
noncomputable def g_sbc5 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (syn_wsbc A x ph) (syn_wex x (syn_wa (.classEq (.cv x) A) ph))) :=
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
  have p0000 := @g_sbcex ph x A
  have p0001 := @g_exsimpl (.classEq (.cv x) A) ph x
  have p0002 :=
    @g_isset x A
      (by
        first
        | (aesop))
  have p0003 :=
    @g_sylibr (syn_wex x (syn_wa (.classEq (.cv x) A) ph))
      (syn_wex x (.classEq (.cv x) A)) (.classMem A (syn_cvv)) p0001 p0002
  have p0004 := @g_dfsbcq2 ph x y A
  have p0005 := @g_eqeq2 (.cv y) A (.cv x)
  have p0006_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) A) (syn_wb (.objEq x y) (.classEq (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_anbi1d (.classEq (.cv y) A) (.objEq x y) (.classEq (.cv x) A) ph p0006_e00_recanon
  have p0007 :=
    @g_exbidv (.classEq (.cv y) A) (syn_wa (.objEq x y) ph)
      (syn_wa (.classEq (.cv x) A) ph) x
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
    @g_sb5 ph x y
      (by
        first
        | (aesop))
  have p0009 :=
    @g_vtoclbg (syn_wsb y x ph) (syn_wex x (syn_wa (.objEq x y) ph)) (syn_wsbc A x ph)
      (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) y A (syn_cvv)
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
    @g_pm5_21nii (syn_wsbc A x ph) (.classMem A (syn_cvv))
      (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) p0000 p0003 p0009
  exact p0010

@[expose]
noncomputable def g_sbc6g (ph : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem A V)
        (syn_wb (syn_wsbc A x ph) (.all x (.imp (.classEq (.cv x) A) ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := @g_nfe1 (syn_wa (.classEq (.cv x) A) ph) x
  have p0001 :=
    @g_ceqex ph x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_ceqsalg ph (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) x A V
      (by
        first
        | (aesop))
      p0000 p0001
  have p0003 :=
    @g_sbc5 ph x A
      (by
        first
        | (aesop))
  have p0004 :=
    @g_syl6rbbr (.classMem A V) (.all x (.imp (.classEq (.cv x) A) ph))
      (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) (syn_wsbc A x ph) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_sbciegft (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (syn_wnf x ps)
          (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps)))) (syn_wb (syn_wsbc A x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_sbc5 ph x A
      (by
        first
        | (aesop))
  have p0001 := @g_bi1 ph ps
  have p0002 := @g_imim2i (syn_wb ph ps) (.imp ph ps) (.classEq (.cv x) A) p0001
  have p0003 :=
    @g_imp3a (.imp (.classEq (.cv x) A) (syn_wb ph ps)) (.classEq (.cv x) A) ph ps p0002
  have p0004 :=
    @g_alimi (.imp (.classEq (.cv x) A) (syn_wb ph ps))
      (.imp (syn_wa (.classEq (.cv x) A) ph) ps) x p0003
  have p0005 := @g_n_19_23t (syn_wa (.classEq (.cv x) A) ph) ps x
  have p0006 :=
    @g_biimpa (syn_wnf x ps) (.all x (.imp (syn_wa (.classEq (.cv x) A) ph) ps))
      (.imp (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps) p0005
  have p0007 :=
    @g_sylan2 (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (syn_wnf x ps)
      (.all x (.imp (syn_wa (.classEq (.cv x) A) ph) ps))
      (.imp (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps) p0004 p0006
  have p0008 :=
    @g_n_3adant1 (syn_wnf x ps) (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
      (.imp (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) ps) (.classMem A V) p0007
  have p0009 :=
    @g_syl5bi (syn_wsbc A x ph) (syn_wex x (syn_wa (.classEq (.cv x) A) ph))
      (syn_w3a (.classMem A V) (syn_wnf x ps)
        (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))))
      ps p0000 p0008
  have p0010 := @g_bi2 ph ps
  have p0011 := @g_imim2i (syn_wb ph ps) (.imp ps ph) (.classEq (.cv x) A) p0010
  have p0012 :=
    @g_com23 (.imp (.classEq (.cv x) A) (syn_wb ph ps)) (.classEq (.cv x) A) ps ph p0011
  have p0013 :=
    @g_alimi (.imp (.classEq (.cv x) A) (syn_wb ph ps))
      (.imp ps (.imp (.classEq (.cv x) A) ph)) x p0012
  have p0014 := @g_n_19_21t ps (.imp (.classEq (.cv x) A) ph) x
  have p0015 :=
    @g_biimpa (syn_wnf x ps) (.all x (.imp ps (.imp (.classEq (.cv x) A) ph)))
      (.imp ps (.all x (.imp (.classEq (.cv x) A) ph))) p0014
  have p0016 :=
    @g_sylan2 (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (syn_wnf x ps)
      (.all x (.imp ps (.imp (.classEq (.cv x) A) ph)))
      (.imp ps (.all x (.imp (.classEq (.cv x) A) ph))) p0013 p0015
  have p0017 :=
    @g_n_3adant1 (syn_wnf x ps) (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
      (.imp ps (.all x (.imp (.classEq (.cv x) A) ph))) (.classMem A V) p0016
  have p0018 :=
    @g_sbc6g ph x A V
      (by
        first
        | (aesop))
  have p0019 :=
    @g_n_3ad2ant1 (.classMem A V) (syn_wnf x ps)
      (syn_wb (syn_wsbc A x ph) (.all x (.imp (.classEq (.cv x) A) ph)))
      (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) p0018
  have p0020 :=
    @g_sylibrd
      (syn_w3a (.classMem A V) (syn_wnf x ps)
        (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))))
      ps (.all x (.imp (.classEq (.cv x) A) ph)) (syn_wsbc A x ph) p0017 p0019
  have p0021 :=
    @g_impbid
      (syn_w3a (.classMem A V) (syn_wnf x ps)
        (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))))
      (syn_wsbc A x ph) ps p0009 p0020
  exact p0021

@[expose]
noncomputable def g_sbciegf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (hyp_sbciegf_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_sbciegf_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (syn_wsbc A x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := Nominal.gen hyp_sbciegf_2 x
  have p0001 :=
    @g_sbciegft ph ps x A V
      (by
        first
        | (aesop))
  have p0002 :=
    @g_mp3an23 (.classMem A V) (syn_wnf x ps)
      (.all x (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (syn_wb (syn_wsbc A x ph) ps)
      hyp_sbciegf_1 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sbcieg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_sbcieg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (syn_wsbc A x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := @g_elex A V
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sbciegf ph ps x A (syn_cvv)
      (by
        first
        | (aesop))
      p0001 hyp_sbcieg_1
  have p0003 :=
    @g_syl (.classMem A V) (.classMem A (syn_cvv)) (syn_wb (syn_wsbc A x ph) ps) p0000
      p0002
  exact p0003

@[expose]
noncomputable def g_sbciedf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (V : Class) (dv_A_x : x ∉ A.fv)
    (hyp_sbcied_1 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_sbcied_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (syn_wb ps ch)))
    (hyp_sbciedf_3 : Nominal.NPrf (syn_wnf x ph))
    (hyp_sbciedf_4 : Nominal.NPrf (.imp ph (syn_wnf x ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wsbc A x ps) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 := @g_ex ph (.classEq (.cv x) A) (syn_wb ps ch) hyp_sbcied_2
  have p0001 :=
    @g_alrimi ph (.imp (.classEq (.cv x) A) (syn_wb ps ch)) x hyp_sbciedf_3 p0000
  have p0002 :=
    @g_sbciegft ps ch x A V
      (by
        first
        | (aesop))
  have p0003 :=
    @g_syl3anc ph (.classMem A V) (syn_wnf x ch)
      (.all x (.imp (.classEq (.cv x) A) (syn_wb ps ch))) (syn_wb (syn_wsbc A x ps) ch)
      hyp_sbcied_1 hyp_sbciedf_4 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_eqsbc1 (x : Var) (A : Class) (B : Class) (V : Class)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (syn_wsbc A x (.classEq (.cv x) B)) (.classEq A B))) :=
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
  have p0000 := @g_dfsbcq (.classEq (.cv x) B) x (.cv y) A
  have p0001 := @g_eqeq1 (.cv y) A B
  have p0002 := @g_sbsbc (.classEq (.cv x) B) x y
  have p0003 :=
    @g_eqsb1 x y B
      (by
        first
        | (aesop))
  have p0004 :=
    @g_bitr3i (syn_wsbc (.cv y) x (.classEq (.cv x) B)) (syn_wsb y x (.classEq (.cv x) B))
      (.classEq (.cv y) B) p0002 p0003
  have p0005 :=
    @g_vtoclbg (syn_wsbc (.cv y) x (.classEq (.cv x) B)) (.classEq (.cv y) B)
      (syn_wsbc A x (.classEq (.cv x) B)) (.classEq A B) y A V
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

@[expose]
noncomputable def g_sbcimg (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (syn_wsbc A x (.imp ph ps))
          (.imp (syn_wsbc A x ph) (syn_wsbc A x ps)))) :=
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
  have p0000 := @g_dfsbcq2 (.imp ph ps) x y A
  have p0001 := @g_dfsbcq2 ph x y A
  have p0002 := @g_dfsbcq2 ps x y A
  have p0003 :=
    @g_imbi12d (.classEq (.cv y) A) (syn_wsb y x ph) (syn_wsbc A x ph) (syn_wsb y x ps)
      (syn_wsbc A x ps) p0001 p0002
  have p0004 := @g_sbim ph ps x y
  have p0005 :=
    @g_vtoclbg (syn_wsb y x (.imp ph ps)) (.imp (syn_wsb y x ph) (syn_wsb y x ps))
      (syn_wsbc A x (.imp ph ps)) (.imp (syn_wsbc A x ph) (syn_wsbc A x ps)) y A V
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

@[expose]
noncomputable def g_sbcan (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wsbc A x (syn_wa ph ps)) (syn_wa (syn_wsbc A x ph) (syn_wsbc A x ps))) :=
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
  have p0000 := @g_sbcex (syn_wa ph ps) x A
  have p0001 := @g_sbcex ps x A
  have p0002 :=
    @g_adantl (syn_wsbc A x ps) (.classMem A (syn_cvv)) (syn_wsbc A x ph) p0001
  have p0003 := @g_dfsbcq2 (syn_wa ph ps) x y A
  have p0004 := @g_dfsbcq2 ph x y A
  have p0005 := @g_dfsbcq2 ps x y A
  have p0006 :=
    @g_anbi12d (.classEq (.cv y) A) (syn_wsb y x ph) (syn_wsbc A x ph) (syn_wsb y x ps)
      (syn_wsbc A x ps) p0004 p0005
  have p0007 := @g_sban ph ps x y
  have p0008 :=
    @g_vtoclbg (syn_wsb y x (syn_wa ph ps)) (syn_wa (syn_wsb y x ph) (syn_wsb y x ps))
      (syn_wsbc A x (syn_wa ph ps)) (syn_wa (syn_wsbc A x ph) (syn_wsbc A x ps)) y A
      (syn_cvv)
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
    @g_pm5_21nii (syn_wsbc A x (syn_wa ph ps)) (.classMem A (syn_cvv))
      (syn_wa (syn_wsbc A x ph) (syn_wsbc A x ps)) p0000 p0002 p0008
  exact p0009

@[expose]
noncomputable def g_sbceqal (x : Var) (A : Class) (B : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (.imp (.all x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)))
          (.classEq A B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  have p0000 := @g_spsbc (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)) x A V
  have p0001 := @g_sbcimg (.classEq (.cv x) A) (.classEq (.cv x) B) x A V
  have p0002 := @g_eqid A
  have p0003 :=
    @g_eqsbc1 x A A V
      (by
        first
        | (aesop))
  have p0004 :=
    @g_mpbiri (.classMem A V) (syn_wsbc A x (.classEq (.cv x) A)) (.classEq A A) p0002
      p0003
  have p0005 :=
    @g_pm5_5 (syn_wsbc A x (.classEq (.cv x) A)) (syn_wsbc A x (.classEq (.cv x) B))
  have p0006 :=
    @g_syl (.classMem A V) (syn_wsbc A x (.classEq (.cv x) A))
      (syn_wb (.imp (syn_wsbc A x (.classEq (.cv x) A)) (syn_wsbc A x (.classEq (.cv x) B)))
        (syn_wsbc A x (.classEq (.cv x) B)))
      p0004 p0005
  have p0007 :=
    @g_eqsbc1 x A B V
      (by
        first
        | (aesop))
  have p0008 :=
    @g_n_3bitrd (.classMem A V)
      (syn_wsbc A x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)))
      (.imp (syn_wsbc A x (.classEq (.cv x) A)) (syn_wsbc A x (.classEq (.cv x) B)))
      (syn_wsbc A x (.classEq (.cv x) B)) (.classEq A B) p0001 p0006 p0007
  have p0009 :=
    @g_sylibd (.classMem A V) (.all x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)))
      (syn_wsbc A x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B))) (.classEq A B) p0000
      p0008
  exact p0009

@[expose]
noncomputable def g_sbeqalb (ph : Wff) (x : Var) (A : Class) (B : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (.imp (syn_wa (.all x (syn_wb ph (.classEq (.cv x) A)))
            (.all x (syn_wb ph (.classEq (.cv x) B)))) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  have p0000 := @g_bibi1 ph (.classEq (.cv x) A) (.classEq (.cv x) B)
  have p0001 :=
    @g_biimpa (syn_wb ph (.classEq (.cv x) A)) (syn_wb ph (.classEq (.cv x) B))
      (syn_wb (.classEq (.cv x) A) (.classEq (.cv x) B)) p0000
  have p0002 :=
    @g_biimpd (syn_wa (syn_wb ph (.classEq (.cv x) A)) (syn_wb ph (.classEq (.cv x) B)))
      (.classEq (.cv x) A) (.classEq (.cv x) B) p0001
  have p0003 :=
    @g_alanimi (syn_wb ph (.classEq (.cv x) A)) (syn_wb ph (.classEq (.cv x) B))
      (.imp (.classEq (.cv x) A) (.classEq (.cv x) B)) x p0002
  have p0004 :=
    @g_sbceqal x A B V
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_syl5
      (syn_wa (.all x (syn_wb ph (.classEq (.cv x) A)))
        (.all x (syn_wb ph (.classEq (.cv x) B))))
      (.all x (.imp (.classEq (.cv x) A) (.classEq (.cv x) B))) (.classMem A V)
      (.classEq A B) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_sbcbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_sbcbid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_sbcbid_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wsbc A x ps) (syn_wsbc A x ch))) :=
  by
  have p0000 := @g_abbid ph ps ch x hyp_sbcbid_1 hyp_sbcbid_2
  have p0001 := @g_eleq2d ph (.cab x ps) (.cab x ch) A p0000
  have p0002 := (Nominal.biimpRefl (syn_wsbc A x ps))
  have p0003 := (Nominal.biimpRefl (syn_wsbc A x ch))
  have p0004 :=
    @g_n_3bitr4g ph (.classMem A (.cab x ps)) (.classMem A (.cab x ch)) (syn_wsbc A x ps)
      (syn_wsbc A x ch) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_sbcbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_sbcbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wsbc A x ps) (syn_wsbc A x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_sbcbid ph ps ch x A p0000 hyp_sbcbidv_1
  exact p0001

@[expose]
noncomputable def g_sbcbii (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_sbcbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wsbc A x ph) (syn_wsbc A x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_a1i (syn_wb ph ps) syn_wtru hyp_sbcbii_1
  have p0001 :=
    @g_sbcbidv syn_wtru ph ps x A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @g_trud (syn_wb (syn_wsbc A x ph) (syn_wsbc A x ps)) p0001
  exact p0002

@[expose]
noncomputable def g_sbccomlem (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wsbc A x (syn_wsbc B y ph)) (syn_wsbc B y (syn_wsbc A x ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_excom (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph)) x y
  have p0001 :=
    @g_exdistr (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph) x y
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
  have p0002 := @g_an12 (.classEq (.cv x) A) (.classEq (.cv y) B) ph
  have p0003 :=
    @g_exbii (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph))
      (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv x) A) ph)) x p0002
  have p0004 :=
    @g_n_19_42v (.classEq (.cv y) B) (syn_wa (.classEq (.cv x) A) ph) x
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
    @g_bitri (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph)))
      (syn_wex x (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv x) A) ph)))
      (syn_wa (.classEq (.cv y) B) (syn_wex x (syn_wa (.classEq (.cv x) A) ph))) p0003
      p0004
  have p0006 :=
    @g_exbii (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph)))
      (syn_wa (.classEq (.cv y) B) (syn_wex x (syn_wa (.classEq (.cv x) A) ph))) y p0005
  have p0007 :=
    @g_n_3bitr3i
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (.cv y) B) ph))))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) B) ph))))
      (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex x (syn_wa (.classEq (.cv x) A) ph))))
      p0000 p0001 p0006
  have p0008 :=
    @g_sbc5 (syn_wex y (syn_wa (.classEq (.cv y) B) ph)) x A
      (by
        first
        | (aesop))
  have p0009 :=
    @g_sbc5 (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) y B
      (by
        first
        | (aesop))
  have p0010 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) B) ph))))
      (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex x (syn_wa (.classEq (.cv x) A) ph))))
      (syn_wsbc A x (syn_wex y (syn_wa (.classEq (.cv y) B) ph)))
      (syn_wsbc B y (syn_wex x (syn_wa (.classEq (.cv x) A) ph))) p0007 p0008 p0009
  have p0011 :=
    @g_sbc5 ph y B
      (by
        first
        | (aesop))
  have p0012 :=
    @g_sbcbii (syn_wsbc B y ph) (syn_wex y (syn_wa (.classEq (.cv y) B) ph)) x A p0011
  have p0013 :=
    @g_sbc5 ph x A
      (by
        first
        | (aesop))
  have p0014 :=
    @g_sbcbii (syn_wsbc A x ph) (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) y B p0013
  have p0015 :=
    @g_n_3bitr4i (syn_wsbc A x (syn_wex y (syn_wa (.classEq (.cv y) B) ph)))
      (syn_wsbc B y (syn_wex x (syn_wa (.classEq (.cv x) A) ph)))
      (syn_wsbc A x (syn_wsbc B y ph)) (syn_wsbc B y (syn_wsbc A x ph)) p0010 p0012 p0014
  exact p0015

@[expose]
noncomputable def g_sbccom (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wsbc A x (syn_wsbc B y ph)) (syn_wsbc B y (syn_wsbc A x ph))) :=
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
    @g_sbccomlem (syn_wsbc (.cv w) y (syn_wsbc (.cv z) x ph)) z w A B fresh_z_not_A
      fresh_w_not_A fresh_z_not_B fresh_w_not_B fresh_z_ne_w
  have p0001 :=
    @g_sbccomlem ph y x (.cv w) (.cv z) (not_mem_class_variable _ _ fresh_y_ne_w)
      (not_mem_class_variable _ _ fresh_x_ne_w) (not_mem_class_variable _ _ fresh_y_ne_z)
      (not_mem_class_variable _ _ fresh_x_ne_z) (Ne.symm dv_x_y)
  have p0002 :=
    @g_sbcbii (syn_wsbc (.cv w) y (syn_wsbc (.cv z) x ph))
      (syn_wsbc (.cv z) x (syn_wsbc (.cv w) y ph)) w B p0001
  have p0003 :=
    @g_sbccomlem (syn_wsbc (.cv w) y ph) w x B (.cv z) fresh_w_not_B dv_B_x
      (not_mem_class_variable _ _ fresh_w_ne_z) (not_mem_class_variable _ _ fresh_x_ne_z)
      fresh_w_ne_x
  have p0004 :=
    @g_bitri (syn_wsbc B w (syn_wsbc (.cv w) y (syn_wsbc (.cv z) x ph)))
      (syn_wsbc B w (syn_wsbc (.cv z) x (syn_wsbc (.cv w) y ph)))
      (syn_wsbc (.cv z) x (syn_wsbc B w (syn_wsbc (.cv w) y ph))) p0002 p0003
  have p0005 :=
    @g_sbcbii (syn_wsbc B w (syn_wsbc (.cv w) y (syn_wsbc (.cv z) x ph)))
      (syn_wsbc (.cv z) x (syn_wsbc B w (syn_wsbc (.cv w) y ph))) z A p0004
  have p0006 :=
    @g_sbccomlem (syn_wsbc (.cv z) x ph) z y A (.cv w) fresh_z_not_A dv_A_y
      (not_mem_class_variable _ _ fresh_z_ne_w) (not_mem_class_variable _ _ fresh_y_ne_w)
      fresh_z_ne_y
  have p0007 :=
    @g_sbcbii (syn_wsbc A z (syn_wsbc (.cv w) y (syn_wsbc (.cv z) x ph)))
      (syn_wsbc (.cv w) y (syn_wsbc A z (syn_wsbc (.cv z) x ph))) w B p0006
  have p0008 :=
    @g_n_3bitr3i
      (syn_wsbc A z (syn_wsbc B w (syn_wsbc (.cv w) y (syn_wsbc (.cv z) x ph))))
      (syn_wsbc B w (syn_wsbc A z (syn_wsbc (.cv w) y (syn_wsbc (.cv z) x ph))))
      (syn_wsbc A z (syn_wsbc (.cv z) x (syn_wsbc B w (syn_wsbc (.cv w) y ph))))
      (syn_wsbc B w (syn_wsbc (.cv w) y (syn_wsbc A z (syn_wsbc (.cv z) x ph)))) p0000
      p0005 p0007
  have p0009 :=
    @g_sbcco (syn_wsbc B w (syn_wsbc (.cv w) y ph)) x z A
      (not_mem_syn_wsbc z B w _ fresh_z_not_B
        (not_mem_syn_wsbc z (.cv w) y ph (not_mem_class_variable _ _ fresh_z_ne_w)
          fresh_z_not_ph))
  have p0010 :=
    @g_sbcco (syn_wsbc A z (syn_wsbc (.cv z) x ph)) y w B
      (not_mem_syn_wsbc w A z _ fresh_w_not_A
        (not_mem_syn_wsbc w (.cv z) x ph (not_mem_class_variable _ _ fresh_w_ne_z)
          fresh_w_not_ph))
  have p0011 :=
    @g_n_3bitr3i
      (syn_wsbc A z (syn_wsbc (.cv z) x (syn_wsbc B w (syn_wsbc (.cv w) y ph))))
      (syn_wsbc B w (syn_wsbc (.cv w) y (syn_wsbc A z (syn_wsbc (.cv z) x ph))))
      (syn_wsbc A x (syn_wsbc B w (syn_wsbc (.cv w) y ph)))
      (syn_wsbc B y (syn_wsbc A z (syn_wsbc (.cv z) x ph))) p0008 p0009 p0010
  have p0012 := @g_sbcco ph y w B fresh_w_not_ph
  have p0013 :=
    @g_sbcbii (syn_wsbc B w (syn_wsbc (.cv w) y ph)) (syn_wsbc B y ph) x A p0012
  have p0014 := @g_sbcco ph x z A fresh_z_not_ph
  have p0015 :=
    @g_sbcbii (syn_wsbc A z (syn_wsbc (.cv z) x ph)) (syn_wsbc A x ph) y B p0014
  have p0016 :=
    @g_n_3bitr3i (syn_wsbc A x (syn_wsbc B w (syn_wsbc (.cv w) y ph)))
      (syn_wsbc B y (syn_wsbc A z (syn_wsbc (.cv z) x ph)))
      (syn_wsbc A x (syn_wsbc B y ph)) (syn_wsbc B y (syn_wsbc A x ph)) p0011 p0013 p0015
  exact p0016

@[expose]
noncomputable def g_rspesbca (ph : Wff) (x : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A B) (syn_wsbc A x ph)) (syn_wrex x B ph)) :=
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
  have p0000 := @g_dfsbcq2 ph x y A
  have p0001 :=
    @g_rspcev (syn_wsb y x ph) (syn_wsbc A x ph) y A B
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
    @g_cbvrexsv ph x y B
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
    @g_sylibr (syn_wa (.classMem A B) (syn_wsbc A x ph)) (syn_wrex y B (syn_wsb y x ph))
      (syn_wrex x B ph) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_spesbc (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wsbc A x ph) (syn_wex x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_sbcex ph x A
  have p0001 :=
    @g_rspesbca ph x A (syn_cvv)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
  have p0002 :=
    @g_mpancom (.classMem A (syn_cvv)) (syn_wsbc A x ph) (syn_wrex x (syn_cvv) ph) p0000
      p0001
  have p0003 := @g_rexv ph x
  have p0004 :=
    @g_sylib (syn_wsbc A x ph) (syn_wrex x (syn_cvv) ph) (syn_wex x ph) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_csbeq1 (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_csb A x C) (syn_csb B x C))) :=
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
  have p0000 := @g_dfsbcq (.classMem (.cv y) C) x A B
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wsbc A x (.classMem (.cv y) C))
      (syn_wsbc B x (.classMem (.cv y) C)) y
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_csb x y A C
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_csb x y B C
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
    @g_n_3eqtr4g (.classEq A B) (.cab y (syn_wsbc A x (.classMem (.cv y) C)))
      (.cab y (syn_wsbc B x (.classMem (.cv y) C))) (syn_csb A x C) (syn_csb B x C) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_csbeq1d (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (hyp_csbeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csb A x C) (syn_csb B x C))) :=
  by
  have p0000 := @g_csbeq1 x A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_csb A x C) (syn_csb B x C)) hyp_csbeq1d_1
      p0000
  exact p0001

@[expose]
noncomputable def g_csbid (x : Var) (A : Class) :
    Nominal.NPrf (.classEq (syn_csb (.cv x) x A) A) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_csb x y (.cv x) A
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
  have p0001 := @g_sbsbc (.classMem (.cv y) A) x x
  have p0002 := @g_sbid (.classMem (.cv y) A) x
  have p0003 :=
    @g_bitr3i (syn_wsbc (.cv x) x (.classMem (.cv y) A))
      (syn_wsb x x (.classMem (.cv y) A)) (.classMem (.cv y) A) p0001 p0002
  have p0004 :=
    @g_abbii (syn_wsbc (.cv x) x (.classMem (.cv y) A)) (.classMem (.cv y) A) y p0003
  have p0005 :=
    @g_abid2 y A
      (by
        first
        | (aesop))
  have p0006 :=
    @g_n_3eqtri (syn_csb (.cv x) x A) (.cab y (syn_wsbc (.cv x) x (.classMem (.cv y) A)))
      (.cab y (.classMem (.cv y) A)) A p0000 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_csbeq1a (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B (syn_csb A x B))) :=
  by
  have p0000 := @g_csbid x B
  have p0001 := @g_csbeq1 x (.cv x) A B
  have p0002 :=
    @g_syl5eqr (.classEq (.cv x) A) B (syn_csb (.cv x) x B) (syn_csb A x B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_csbeq2d (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (hyp_csbeq2d_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_csbeq2d_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csb A x B) (syn_csb A x C))) :=
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
  have p0000 := @g_eleq2d ph B C (.cv y) hyp_csbeq2d_2
  have p0001 :=
    @g_sbcbid ph (.classMem (.cv y) B) (.classMem (.cv y) C) x A hyp_csbeq2d_1 p0000
  have p0002 :=
    @g_abbidv ph (syn_wsbc A x (.classMem (.cv y) B)) (syn_wsbc A x (.classMem (.cv y) C))
      y
      (by
        first
        | (aesop))
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_csb x y A B
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_csb x y A C
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
    @g_n_3eqtr4g ph (.cab y (syn_wsbc A x (.classMem (.cv y) B)))
      (.cab y (syn_wsbc A x (.classMem (.cv y) C))) (syn_csb A x B) (syn_csb A x C) p0002
      p0003 p0004
  exact p0005

@[expose]
noncomputable def g_csbeq2dv (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_csbeq2dv_1 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csb A x B) (syn_csb A x C))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_csbeq2d ph x A B C p0000 hyp_csbeq2dv_1
  exact p0001

@[expose]
noncomputable def g_nfcsb1d (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfcsb1d_1 : Nominal.NPrf (.imp ph (syn_wnfc x A))) :
    Nominal.NPrf (.imp ph (syn_wnfc x (syn_csb A x B))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_csb x y A B
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
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0002 := @g_nfsbc1d ph (.classMem (.cv y) B) x A hyp_nfcsb1d_1
  have p0003 := @g_nfabd ph (syn_wsbc A x (.classMem (.cv y) B)) x y p0001 p0002
  have p0004 :=
    @g_nfcxfrd ph x (syn_csb A x B) (.cab y (syn_wsbc A x (.classMem (.cv y) B))) p0000
      p0003
  exact p0004

@[expose]
noncomputable def g_nfcsb1 (x : Var) (A : Class) (B : Class)
    (hyp_nfcsb1_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wnfc x (syn_csb A x B)) :=
  by
  have p0000 := @g_a1i (syn_wnfc x A) syn_wtru hyp_nfcsb1_1
  have p0001 := @g_nfcsb1d syn_wtru x A B p0000
  have p0002 := @g_trud (syn_wnfc x (syn_csb A x B)) p0001
  exact p0002

@[expose]
noncomputable def g_nfcsb1v (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wnfc x (syn_csb A x B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 := @g_nfcsb1 x A B p0000
  exact p0001

@[expose]
noncomputable def g_nfcsbd (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_nfcsbd_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfcsbd_2 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_nfcsbd_3 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wnfc x (syn_csb A y B))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_csb y z A B
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
    @g_nfv ph z
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfcrd ph x z B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_nfcsbd_3
  have p0003 := @g_nfsbcd ph (.classMem (.cv z) B) x y A hyp_nfcsbd_1 hyp_nfcsbd_2 p0002
  have p0004 := @g_nfabd ph (syn_wsbc A y (.classMem (.cv z) B)) x z p0001 p0003
  have p0005 :=
    @g_nfcxfrd ph x (syn_csb A y B) (.cab z (syn_wsbc A y (.classMem (.cv z) B))) p0000
      p0004
  exact p0005

@[expose]
noncomputable def g_nfcsb (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_nfcsb_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfcsb_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnfc x (syn_csb A y B)) :=
  by
  have p0000 := @g_nftru y
  have p0001 := @g_a1i (syn_wnfc x A) syn_wtru hyp_nfcsb_1
  have p0002 := @g_a1i (syn_wnfc x B) syn_wtru hyp_nfcsb_2
  have p0003 := @g_nfcsbd syn_wtru x y A B p0000 p0001 p0002
  have p0004 := @g_trud (syn_wnfc x (syn_csb A y B)) p0003
  exact p0004

@[expose]
noncomputable def g_csbiebt (x : Var) (A : Class) (B : Class) (C : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (syn_wnfc x C))
        (syn_wb (.all x (.imp (.classEq (.cv x) A) (.classEq B C)))
          (.classEq (syn_csb A x B) C))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  have p0000 := @g_elex A V
  have p0001 := @g_spsbc (.imp (.classEq (.cv x) A) (.classEq B C)) x A (syn_cvv)
  have p0002 :=
    @g_adantr (.classMem A (syn_cvv))
      (.imp (.all x (.imp (.classEq (.cv x) A) (.classEq B C)))
        (syn_wsbc A x (.imp (.classEq (.cv x) A) (.classEq B C))))
      (syn_wnfc x C) p0001
  have p0003 := @g_simpl (.classMem A (syn_cvv)) (syn_wnfc x C)
  have p0004 := @g_biimt (.classEq (.cv x) A) (.classEq B C)
  have p0005 := @g_csbeq1a x A B
  have p0006 := @g_eqeq1d (.classEq (.cv x) A) B (syn_csb A x B) C p0005
  have p0007 :=
    @g_bitr3d (.classEq (.cv x) A) (.classEq B C)
      (.imp (.classEq (.cv x) A) (.classEq B C)) (.classEq (syn_csb A x B) C) p0004 p0006
  have p0008 :=
    @g_adantl (.classEq (.cv x) A)
      (syn_wb (.imp (.classEq (.cv x) A) (.classEq B C)) (.classEq (syn_csb A x B) C))
      (syn_wa (.classMem A (syn_cvv)) (syn_wnfc x C)) p0007
  have p0009 :=
    @g_nfv (.classMem A (syn_cvv)) x
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
  have p0010 := @g_nfnfc1 x C
  have p0011 := @g_nfan (.classMem A (syn_cvv)) (syn_wnfc x C) x p0009 p0010
  have p0012 :=
    @g_nfcsb1v x A B
      (by
        first
        | (aesop))
  have p0013 :=
    @g_a1i (syn_wnfc x (syn_csb A x B)) (syn_wa (.classMem A (syn_cvv)) (syn_wnfc x C))
      p0012
  have p0014 := @g_simpr (.classMem A (syn_cvv)) (syn_wnfc x C)
  have p0015 :=
    @g_nfeqd (syn_wa (.classMem A (syn_cvv)) (syn_wnfc x C)) x (syn_csb A x B) C p0013
      p0014
  have p0016 :=
    @g_sbciedf (syn_wa (.classMem A (syn_cvv)) (syn_wnfc x C))
      (.imp (.classEq (.cv x) A) (.classEq B C)) (.classEq (syn_csb A x B) C) x A
      (syn_cvv)
      (by
        first
        | (aesop))
      p0003 p0008 p0011 p0015
  have p0017 :=
    @g_sylibd (syn_wa (.classMem A (syn_cvv)) (syn_wnfc x C))
      (.all x (.imp (.classEq (.cv x) A) (.classEq B C)))
      (syn_wsbc A x (.imp (.classEq (.cv x) A) (.classEq B C)))
      (.classEq (syn_csb A x B) C) p0002 p0016
  have p0018 := @g_a1i (syn_wnfc x (syn_csb A x B)) (syn_wnfc x C) p0012
  have p0019 := @g_id (syn_wnfc x C)
  have p0020 := @g_nfeqd (syn_wnfc x C) x (syn_csb A x B) C p0018 p0019
  have p0021 := @g_nfan1 (syn_wnfc x C) (.classEq (syn_csb A x B) C) x p0010 p0020
  have p0022 :=
    @g_biimprcd (.classEq (.cv x) A) (.classEq B C) (.classEq (syn_csb A x B) C) p0006
  have p0023 :=
    @g_adantl (.classEq (syn_csb A x B) C) (.imp (.classEq (.cv x) A) (.classEq B C))
      (syn_wnfc x C) p0022
  have p0024 :=
    @g_alrimi (syn_wa (syn_wnfc x C) (.classEq (syn_csb A x B) C))
      (.imp (.classEq (.cv x) A) (.classEq B C)) x p0021 p0023
  have p0025 :=
    @g_ex (syn_wnfc x C) (.classEq (syn_csb A x B) C)
      (.all x (.imp (.classEq (.cv x) A) (.classEq B C))) p0024
  have p0026 :=
    @g_adantl (syn_wnfc x C)
      (.imp (.classEq (syn_csb A x B) C) (.all x (.imp (.classEq (.cv x) A) (.classEq B C))))
      (.classMem A (syn_cvv)) p0025
  have p0027 :=
    @g_impbid (syn_wa (.classMem A (syn_cvv)) (syn_wnfc x C))
      (.all x (.imp (.classEq (.cv x) A) (.classEq B C))) (.classEq (syn_csb A x B) C)
      p0017 p0026
  have p0028 :=
    @g_sylan (.classMem A V) (.classMem A (syn_cvv)) (syn_wnfc x C)
      (syn_wb (.all x (.imp (.classEq (.cv x) A) (.classEq B C))) (.classEq (syn_csb A x B) C))
      p0000 p0027
  exact p0028

@[expose]
noncomputable def g_csbiedf (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (V : Class) (dv_A_x : x ∉ A.fv) (hyp_csbiedf_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_csbiedf_2 : Nominal.NPrf (.imp ph (syn_wnfc x C)))
    (hyp_csbiedf_3 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_csbiedf_4 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csb A x B) C)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  have p0000 := @g_ex ph (.classEq (.cv x) A) (.classEq B C) hyp_csbiedf_4
  have p0001 :=
    @g_alrimi ph (.imp (.classEq (.cv x) A) (.classEq B C)) x hyp_csbiedf_1 p0000
  have p0002 :=
    @g_csbiebt x A B C V
      (by
        first
        | (aesop))
  have p0003 :=
    @g_syl2anc ph (.classMem A V) (syn_wnfc x C)
      (syn_wb (.all x (.imp (.classEq (.cv x) A) (.classEq B C))) (.classEq (syn_csb A x B) C))
      hyp_csbiedf_3 hyp_csbiedf_2 p0002
  have p0004 :=
    @g_mpbid ph (.all x (.imp (.classEq (.cv x) A) (.classEq B C)))
      (.classEq (syn_csb A x B) C) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_csbied (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (V : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_csbied_1 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_csbied_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csb A x B) C)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcvd ph x C
      (by
        first
        | (aesop))
  have p0002 :=
    @g_csbiedf ph x A B C V
      (by
        first
        | (aesop))
      p0000 p0001 hyp_csbied_1 hyp_csbied_2
  exact p0002

@[expose]
noncomputable def g_elning (A : Class) (B : Class) (C : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classMem A (syn_cnin B C))
          (syn_wnan (.classMem A B) (.classMem A C)))) :=
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
  have p0000 := @g_eleq1 (.cv x) A B
  have p0001 := @g_eleq1 (.cv x) A C
  have p0002 :=
    @g_nanbi12d (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B)
      (.classMem (.cv x) C) (.classMem A C) p0000 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nin x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_elab2g (syn_wnan (.classMem (.cv x) B) (.classMem (.cv x) C))
      (syn_wnan (.classMem A B) (.classMem A C)) x A (syn_cnin B C) V
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

@[expose]
noncomputable def g_elcomplg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classMem A (syn_ccompl B)) (.neg (.classMem A B)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_ccompl B))
  have p0001 := @g_eleq2i (syn_ccompl B) (syn_cnin B B) A p0000
  have p0002 := @g_elning A B B V
  have p0003 := (Nominal.biimpRefl (syn_wnan (.classMem A B) (.classMem A B)))
  have p0004 := @g_anidm (.classMem A B)
  have p0005 :=
    @g_xchbinx (syn_wnan (.classMem A B) (.classMem A B))
      (syn_wa (.classMem A B) (.classMem A B)) (.classMem A B) p0003 p0004
  have p0006 :=
    @g_syl6bb (.classMem A V) (.classMem A (syn_cnin B B))
      (syn_wnan (.classMem A B) (.classMem A B)) (.neg (.classMem A B)) p0002 p0005
  have p0007 :=
    @g_syl5bb (.classMem A (syn_ccompl B)) (.classMem A (syn_cnin B B)) (.classMem A V)
      (.neg (.classMem A B)) p0001 p0006
  exact p0007

@[expose]
noncomputable def g_elin (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cin B C)) (syn_wa (.classMem A B) (.classMem A C))) :=
  by
  have p0000 := @g_elex A (syn_cin B C)
  have p0001 := @g_elex A B
  have p0002 := @g_adantr (.classMem A B) (.classMem A (syn_cvv)) (.classMem A C) p0001
  have p0003 := @g_elcomplg A (syn_cnin B C) (syn_cvv)
  have p0004 := @g_elning A B C (syn_cvv)
  have p0005 :=
    @g_notbid (.classMem A (syn_cvv)) (.classMem A (syn_cnin B C))
      (syn_wnan (.classMem A B) (.classMem A C)) p0004
  have p0006 :=
    @g_bitrd (.classMem A (syn_cvv)) (.classMem A (syn_ccompl (syn_cnin B C)))
      (.neg (.classMem A (syn_cnin B C)))
      (.neg (syn_wnan (.classMem A B) (.classMem A C))) p0003 p0005
  have p0007 := (Nominal.classEqRefl (syn_cin B C))
  have p0008 := @g_eleq2i (syn_cin B C) (syn_ccompl (syn_cnin B C)) A p0007
  have p0009 := (Nominal.biimpRefl (syn_wnan (.classMem A B) (.classMem A C)))
  have p0010 :=
    @g_con2bii (syn_wnan (.classMem A B) (.classMem A C))
      (syn_wa (.classMem A B) (.classMem A C)) p0009
  have p0011 :=
    @g_n_3bitr4g (.classMem A (syn_cvv)) (.classMem A (syn_ccompl (syn_cnin B C)))
      (.neg (syn_wnan (.classMem A B) (.classMem A C))) (.classMem A (syn_cin B C))
      (syn_wa (.classMem A B) (.classMem A C)) p0006 p0008 p0010
  have p0012 :=
    @g_pm5_21nii (.classMem A (syn_cin B C)) (.classMem A (syn_cvv))
      (syn_wa (.classMem A B) (.classMem A C)) p0000 p0002 p0011
  exact p0012

@[expose]
noncomputable def g_elun (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cun B C)) (syn_wo (.classMem A B) (.classMem A C))) :=
  by
  have p0000 := @g_elex A (syn_cun B C)
  have p0001 := @g_elex A B
  have p0002 := @g_elex A C
  have p0003 :=
    @g_jaoi (.classMem A B) (.classMem A (syn_cvv)) (.classMem A C) p0001 p0002
  have p0004 := @g_elning A (syn_ccompl B) (syn_ccompl C) (syn_cvv)
  have p0005 := @g_elcomplg A B (syn_cvv)
  have p0006 := @g_elcomplg A C (syn_cvv)
  have p0007 :=
    @g_nanbi12d (.classMem A (syn_cvv)) (.classMem A (syn_ccompl B))
      (.neg (.classMem A B)) (.classMem A (syn_ccompl C)) (.neg (.classMem A C)) p0005
      p0006
  have p0008 :=
    @g_bitrd (.classMem A (syn_cvv))
      (.classMem A (syn_cnin (syn_ccompl B) (syn_ccompl C)))
      (syn_wnan (.classMem A (syn_ccompl B)) (.classMem A (syn_ccompl C)))
      (syn_wnan (.neg (.classMem A B)) (.neg (.classMem A C))) p0004 p0007
  have p0009 := (Nominal.classEqRefl (syn_cun B C))
  have p0010 := @g_eleq2i (syn_cun B C) (syn_cnin (syn_ccompl B) (syn_ccompl C)) A p0009
  have p0011 := @g_oran (.classMem A B) (.classMem A C)
  have p0012 :=
    (Nominal.biimpRefl (syn_wnan (.neg (.classMem A B)) (.neg (.classMem A C))))
  have p0013 :=
    @g_bitr4i (syn_wo (.classMem A B) (.classMem A C))
      (.neg (syn_wa (.neg (.classMem A B)) (.neg (.classMem A C))))
      (syn_wnan (.neg (.classMem A B)) (.neg (.classMem A C))) p0011 p0012
  have p0014 :=
    @g_n_3bitr4g (.classMem A (syn_cvv))
      (.classMem A (syn_cnin (syn_ccompl B) (syn_ccompl C)))
      (syn_wnan (.neg (.classMem A B)) (.neg (.classMem A C))) (.classMem A (syn_cun B C))
      (syn_wo (.classMem A B) (.classMem A C)) p0008 p0010 p0013
  have p0015 :=
    @g_pm5_21nii (.classMem A (syn_cun B C)) (.classMem A (syn_cvv))
      (syn_wo (.classMem A B) (.classMem A C)) p0000 p0003 p0014
  exact p0015

@[expose]
noncomputable def g_eldif (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cdif B C)) (syn_wa (.classMem A B) (.neg (.classMem A C)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cdif B C))
  have p0001 := @g_eleq2i (syn_cdif B C) (syn_cin B (syn_ccompl C)) A p0000
  have p0002 := @g_elin A B (syn_ccompl C)
  have p0003 := @g_elcomplg A C B
  have p0004 :=
    @g_pm5_32i (.classMem A B) (.classMem A (syn_ccompl C)) (.neg (.classMem A C)) p0003
  have p0005 :=
    @g_n_3bitri (.classMem A (syn_cdif B C)) (.classMem A (syn_cin B (syn_ccompl C)))
      (syn_wa (.classMem A B) (.classMem A (syn_ccompl C)))
      (syn_wa (.classMem A B) (.neg (.classMem A C))) p0001 p0002 p0004
  exact p0005

@[expose]
noncomputable def g_elsymdif (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_csymdif B C))
        (.neg (syn_wb (.classMem A B) (.classMem A C)))) :=
  by
  have p0000 := @g_elun A (syn_cdif B C) (syn_cdif C B)
  have p0001 := @g_eldif A B C
  have p0002 := @g_eldif A C B
  have p0003 :=
    @g_orbi12i (.classMem A (syn_cdif B C))
      (syn_wa (.classMem A B) (.neg (.classMem A C))) (.classMem A (syn_cdif C B))
      (syn_wa (.classMem A C) (.neg (.classMem A B))) p0001 p0002
  have p0004 :=
    @g_bitri (.classMem A (syn_cun (syn_cdif B C) (syn_cdif C B)))
      (syn_wo (.classMem A (syn_cdif B C)) (.classMem A (syn_cdif C B)))
      (syn_wo (syn_wa (.classMem A B) (.neg (.classMem A C)))
        (syn_wa (.classMem A C) (.neg (.classMem A B))))
      p0000 p0003
  have p0005 := (Nominal.classEqRefl (syn_csymdif B C))
  have p0006 :=
    @g_eleq2i (syn_csymdif B C) (syn_cun (syn_cdif B C) (syn_cdif C B)) A p0005
  have p0007 := @g_xor (.classMem A B) (.classMem A C)
  have p0008 :=
    @g_n_3bitr4i (.classMem A (syn_cun (syn_cdif B C) (syn_cdif C B)))
      (syn_wo (syn_wa (.classMem A B) (.neg (.classMem A C)))
        (syn_wa (.classMem A C) (.neg (.classMem A B))))
      (.classMem A (syn_csymdif B C)) (.neg (syn_wb (.classMem A B) (.classMem A C)))
      p0004 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_elnin (A : Class) (B : Class) (C : Class)
    (hyp_elbool_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cnin B C)) (syn_wnan (.classMem A B) (.classMem A C))) :=
  by
  have p0000 := @g_elning A B C (syn_cvv)
  have p0001 := Nominal.mp hyp_elbool_1 p0000
  exact p0001

@[expose]
noncomputable def g_elcompl (A : Class) (B : Class)
    (hyp_elbool_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_ccompl B)) (.neg (.classMem A B))) :=
  by
  have p0000 := @g_elcomplg A B (syn_cvv)
  have p0001 := Nominal.mp hyp_elbool_1 p0000
  exact p0001

@[expose]
noncomputable def g_nincom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cnin A B) (syn_cnin B A)) :=
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
  have p0000 := @g_nancom (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @g_vex x
  have p0002 := @g_elnin (.cv x) A B p0001
  have p0003 := @g_elnin (.cv x) B A p0001
  have p0004 :=
    @g_n_3bitr4i (syn_wnan (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wnan (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.classMem (.cv x) (syn_cnin A B)) (.classMem (.cv x) (syn_cnin B A)) p0000 p0002
      p0003
  have p0005 :=
    @g_eqriv x (syn_cnin A B) (syn_cnin B A)
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

@[expose]
noncomputable def g_dblcompl (A : Class) :
    Nominal.NPrf (.classEq (syn_ccompl (syn_ccompl A)) A) :=
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
  have p0000 := @g_vex x
  have p0001 := @g_elcompl (.cv x) (syn_ccompl A) p0000
  have p0002 := @g_elcompl (.cv x) A p0000
  have p0003 := @g_con2bii (.classMem (.cv x) (syn_ccompl A)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_bitr4i (.classMem (.cv x) (syn_ccompl (syn_ccompl A)))
      (.neg (.classMem (.cv x) (syn_ccompl A))) (.classMem (.cv x) A) p0001 p0003
  have p0005 :=
    @g_eqriv x (syn_ccompl (syn_ccompl A)) A
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

@[expose]
noncomputable def g_nfnin (x : Var) (A : Class) (B : Class)
    (hyp_nfnin_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfnin_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnfc x (syn_cnin A B)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nin y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfel2 x (.cv y) A
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
    @g_nfel2 x (.cv y) B
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
  have p0003 := @g_nfnan (.classMem (.cv y) A) (.classMem (.cv y) B) x p0001 p0002
  have p0004 := @g_nfab (syn_wnan (.classMem (.cv y) A) (.classMem (.cv y) B)) x y p0003
  have p0005 :=
    @g_nfcxfr x (syn_cnin A B)
      (.cab y (syn_wnan (.classMem (.cv y) A) (.classMem (.cv y) B))) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_nfcompl (x : Var) (A : Class)
    (hyp_nfbool_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wnfc x (syn_ccompl A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_ccompl A))
  have p0001 := @g_nfnin x A A hyp_nfbool_1 hyp_nfbool_1
  have p0002 := @g_nfcxfr x (syn_ccompl A) (syn_cnin A A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfun (x : Var) (A : Class) (B : Class)
    (hyp_nfbool_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfbool_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnfc x (syn_cun A B)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cun A B))
  have p0001 := @g_nfcompl x A hyp_nfbool_1
  have p0002 := @g_nfcompl x B hyp_nfbool_2
  have p0003 := @g_nfnin x (syn_ccompl A) (syn_ccompl B) p0001 p0002
  have p0004 :=
    @g_nfcxfr x (syn_cun A B) (syn_cnin (syn_ccompl A) (syn_ccompl B)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nineq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cnin A C) (syn_cnin B C))) :=
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
  have p0000 := @g_eleq2 A B (.cv x)
  have p0001 :=
    @g_nanbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @g_abbidv (.classEq A B) (syn_wnan (.classMem (.cv x) A) (.classMem (.cv x) C))
      (syn_wnan (.classMem (.cv x) B) (.classMem (.cv x) C)) x
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nin x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nin x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab x (syn_wnan (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (.cab x (syn_wnan (.classMem (.cv x) B) (.classMem (.cv x) C))) (syn_cnin A C)
      (syn_cnin B C) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_nineq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cnin C A) (syn_cnin C B))) :=
  by
  have p0000 := @g_nineq1 A B C
  have p0001 := @g_nincom A C
  have p0002 := @g_nincom B C
  have p0003 :=
    @g_n_3eqtr3g (.classEq A B) (syn_cnin A C) (syn_cnin B C) (syn_cnin C A)
      (syn_cnin C B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_nineq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (.classEq (syn_cnin A C) (syn_cnin B D))) :=
  by
  have p0000 := @g_nineq1 A B C
  have p0001 := @g_nineq2 C D B
  have p0002 :=
    @g_sylan9eq (.classEq A B) (.classEq C D) (syn_cnin A C) (syn_cnin B C) (syn_cnin B D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nineq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_nineqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_nineq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cnin A C) (syn_cnin B D)) :=
  by
  have p0000 := @g_nineq12 A B C D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (.classEq (syn_cnin A C) (syn_cnin B D))
      hyp_nineqi_1 hyp_nineq12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_nineq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_nineqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cnin C A) (syn_cnin C B))) :=
  by
  have p0000 := @g_nineq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cnin C A) (syn_cnin C B)) hyp_nineqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_compleq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ccompl A) (syn_ccompl B))) :=
  by
  have p0000 := @g_nineq12 A B A B
  have p0001 := @g_anidms (.classEq A B) (.classEq (syn_cnin A A) (syn_cnin B B)) p0000
  have p0002 := (Nominal.classEqRefl (syn_ccompl A))
  have p0003 := (Nominal.classEqRefl (syn_ccompl B))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cnin A A) (syn_cnin B B) (syn_ccompl A)
      (syn_ccompl B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_compleqi (A : Class) (B : Class)
    (hyp_compleqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_ccompl A) (syn_ccompl B)) :=
  by
  have p0000 := @g_compleq A B
  have p0001 := Nominal.mp hyp_compleqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_compleqd (ph : Wff) (A : Class) (B : Class)
    (hyp_compleqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_ccompl A) (syn_ccompl B))) :=
  by
  have p0000 := @g_compleq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_ccompl A) (syn_ccompl B)) hyp_compleqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_difeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cdif A C) (syn_cdif B C))) :=
  by
  have p0000 := @g_nineq1 A B (syn_ccompl C)
  have p0001 :=
    @g_compleqd (.classEq A B) (syn_cnin A (syn_ccompl C)) (syn_cnin B (syn_ccompl C))
      p0000
  have p0002 := (Nominal.classEqRefl (syn_cdif A C))
  have p0003 := (Nominal.classEqRefl (syn_cin A (syn_ccompl C)))
  have p0004 :=
    @g_eqtri (syn_cdif A C) (syn_cin A (syn_ccompl C))
      (syn_ccompl (syn_cnin A (syn_ccompl C))) p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cdif B C))
  have p0006 := (Nominal.classEqRefl (syn_cin B (syn_ccompl C)))
  have p0007 :=
    @g_eqtri (syn_cdif B C) (syn_cin B (syn_ccompl C))
      (syn_ccompl (syn_cnin B (syn_ccompl C))) p0005 p0006
  have p0008 :=
    @g_n_3eqtr4g (.classEq A B) (syn_ccompl (syn_cnin A (syn_ccompl C)))
      (syn_ccompl (syn_cnin B (syn_ccompl C))) (syn_cdif A C) (syn_cdif B C) p0001 p0004
      p0007
  exact p0008

@[expose]
noncomputable def g_difeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cdif C A) (syn_cdif C B))) :=
  by
  have p0000 := @g_compleq A B
  have p0001 := @g_nineq2d (.classEq A B) (syn_ccompl A) (syn_ccompl B) C p0000
  have p0002 :=
    @g_compleqd (.classEq A B) (syn_cnin C (syn_ccompl A)) (syn_cnin C (syn_ccompl B))
      p0001
  have p0003 := (Nominal.classEqRefl (syn_cdif C A))
  have p0004 := (Nominal.classEqRefl (syn_cin C (syn_ccompl A)))
  have p0005 :=
    @g_eqtri (syn_cdif C A) (syn_cin C (syn_ccompl A))
      (syn_ccompl (syn_cnin C (syn_ccompl A))) p0003 p0004
  have p0006 := (Nominal.classEqRefl (syn_cdif C B))
  have p0007 := (Nominal.classEqRefl (syn_cin C (syn_ccompl B)))
  have p0008 :=
    @g_eqtri (syn_cdif C B) (syn_cin C (syn_ccompl B))
      (syn_ccompl (syn_cnin C (syn_ccompl B))) p0006 p0007
  have p0009 :=
    @g_n_3eqtr4g (.classEq A B) (syn_ccompl (syn_cnin C (syn_ccompl A)))
      (syn_ccompl (syn_cnin C (syn_ccompl B))) (syn_cdif C A) (syn_cdif C B) p0002 p0005
      p0008
  exact p0009

@[expose]
noncomputable def g_dfss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq A (syn_cin A B))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wss A B))
  have p0001 := @g_eqcom (syn_cin A B) A
  have p0002 :=
    @g_bitri (syn_wss A B) (.classEq (syn_cin A B) A) (.classEq A (syn_cin A B)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_dfss2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (syn_wss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_dfss A B
  have p0001 :=
    @g_dfcleq x A (syn_cin A B)
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
  have p0002 := @g_elin (.cv x) A B
  have p0003 :=
    @g_bibi2i (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_albii (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin A B)))
      (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      x p0003
  have p0005 :=
    @g_bitri (.classEq A (syn_cin A B))
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin A B))))
      (.all x (syn_wb (.classMem (.cv x) A)
          (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))))
      p0001 p0004
  have p0006 :=
    @g_bitri (syn_wss A B) (.classEq A (syn_cin A B))
      (.all x (syn_wb (.classMem (.cv x) A)
          (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))))
      p0000 p0005
  have p0007 := @g_pm4_71 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0008 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      x p0007
  have p0009 :=
    @g_bitr4i (syn_wss A B)
      (.all x (syn_wb (.classMem (.cv x) A)
          (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) p0006 p0008
  exact p0009

@[expose]
noncomputable def g_dfss3 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (syn_wss A B) (syn_wral x A (.classMem (.cv x) B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (syn_wral x A (.classMem (.cv x) B)))
  have p0002 :=
    @g_bitr4i (syn_wss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wral x A (.classMem (.cv x) B)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_dfss2f (x : Var) (A : Class) (B : Class)
    (hyp_dfss2f_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_dfss2f_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf
      (syn_wb (syn_wss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
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
    @g_dfss2 z A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcri x z A
      (by
        first
        | (aesop))
      hyp_dfss2f_1
  have p0002 :=
    @g_nfcri x z B
      (by
        first
        | (aesop))
      hyp_dfss2f_2
  have p0003 := @g_nfim (.classMem (.cv z) A) (.classMem (.cv z) B) x p0001 p0002
  have p0004 :=
    @g_nfv (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @g_eleq1 (.cv z) (.cv x) A
  have p0006 := @g_eleq1 (.cv z) (.cv x) B
  have p0007 :=
    @g_imbi12d (.classEq (.cv z) (.cv x)) (.classMem (.cv z) A) (.classMem (.cv x) A)
      (.classMem (.cv z) B) (.classMem (.cv x) B) p0005 p0006
  have p0008_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (syn_wb (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))
          (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_cbval (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) z x p0003 p0004 p0008_e02_recanon
  have p0009 :=
    @g_bitri (syn_wss A B) (.all z (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_ssel (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (.imp (.classMem C A) (.classMem C B))) :=
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
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_biimpi (syn_wss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0000
  have p0002 :=
    @g_n_19_21bi (syn_wss A B) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0001
  have p0003 :=
    @g_anim2d (syn_wss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classEq (.cv x) C) p0002
  have p0004 :=
    @g_eximdv (syn_wss A B) (syn_wa (.classEq (.cv x) C) (.classMem (.cv x) A))
      (syn_wa (.classEq (.cv x) C) (.classMem (.cv x) B)) x
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
    @g_n_3imtr4g (syn_wss A B)
      (syn_wex x (syn_wa (.classEq (.cv x) C) (.classMem (.cv x) A)))
      (syn_wex x (syn_wa (.classEq (.cv x) C) (.classMem (.cv x) B))) (.classMem C A)
      (.classMem C B) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_ssel2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wss A B) (.classMem C A)) (.classMem C B)) :=
  by
  have p0000 := @g_ssel A B C
  have p0001 := @g_imp (syn_wss A B) (.classMem C A) (.classMem C B) p0000
  exact p0001

@[expose]
noncomputable def g_sseli (A : Class) (B : Class) (C : Class)
    (hyp_sseli_1 : Nominal.NPrf (syn_wss A B)) :
    Nominal.NPrf (.imp (.classMem C A) (.classMem C B)) :=
  by
  have p0000 := @g_ssel A B C
  have p0001 := Nominal.mp hyp_sseli_1 p0000
  exact p0001

@[expose]
noncomputable def g_sselii (A : Class) (B : Class) (C : Class)
    (hyp_sseli_1 : Nominal.NPrf (syn_wss A B))
    (hyp_sselii_2 : Nominal.NPrf (.classMem C A)) : Nominal.NPrf (.classMem C B) :=
  by
  have p0000 := @g_sseli A B C hyp_sseli_1
  have p0001 := Nominal.mp hyp_sselii_2 p0000
  exact p0001

@[expose]
noncomputable def g_sseldi (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseli_1 : Nominal.NPrf (syn_wss A B))
    (hyp_sseldi_2 : Nominal.NPrf (.imp ph (.classMem C A))) :
    Nominal.NPrf (.imp ph (.classMem C B)) :=
  by
  have p0000 := @g_sseli A B C hyp_sseli_1
  have p0001 := @g_syl ph (.classMem C A) (.classMem C B) hyp_sseldi_2 p0000
  exact p0001

@[expose]
noncomputable def g_sseld (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseld_1 : Nominal.NPrf (.imp ph (syn_wss A B))) :
    Nominal.NPrf (.imp ph (.imp (.classMem C A) (.classMem C B))) :=
  by
  have p0000 := @g_ssel A B C
  have p0001 :=
    @g_syl ph (syn_wss A B) (.imp (.classMem C A) (.classMem C B)) hyp_sseld_1 p0000
  exact p0001

@[expose]
noncomputable def g_sselda (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseld_1 : Nominal.NPrf (.imp ph (syn_wss A B))) :
    Nominal.NPrf (.imp (syn_wa ph (.classMem C A)) (.classMem C B)) :=
  by
  have p0000 := @g_sseld ph A B C hyp_sseld_1
  have p0001 := @g_imp ph (.classMem C A) (.classMem C B) p0000
  exact p0001

@[expose]
noncomputable def g_sseldd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseld_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_sseldd_2 : Nominal.NPrf (.imp ph (.classMem C A))) :
    Nominal.NPrf (.imp ph (.classMem C B)) :=
  by
  have p0000 := @g_sseld ph A B C hyp_sseld_1
  have p0001 := @g_mpd ph (.classMem C A) (.classMem C B) hyp_sseldd_2 p0000
  exact p0001

@[expose]
noncomputable def g_ssriv (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv)
    (hyp_ssriv_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) :
    Nominal.NPrf (syn_wss A B) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mpgbir (syn_wss A B) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0000
      hyp_ssriv_1
  exact p0001

@[expose]
noncomputable def g_ssrdv (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_ssrdv_1 : Nominal.NPrf (.imp ph (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :
    Nominal.NPrf (.imp ph (syn_wss A B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_alrimiv ph (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      (by
        first
        | (aesop))
      hyp_ssrdv_1
  have p0001 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sylibr ph (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wss A B)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sstr2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (.imp (syn_wss B C) (syn_wss A C))) :=
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
  have p0000 := @g_ssel A B (.cv x)
  have p0001 :=
    @g_imim1d (syn_wss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @g_alimdv (syn_wss A B) (.imp (.classMem (.cv x) B) (.classMem (.cv x) C))
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
    @g_dfss2 x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_dfss2 x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_n_3imtr4g (syn_wss A B) (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))) (syn_wss B C)
      (syn_wss A C) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_sstr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wss A B) (syn_wss B C)) (syn_wss A C)) :=
  by
  have p0000 := @g_sstr2 A B C
  have p0001 := @g_imp (syn_wss A B) (syn_wss B C) (syn_wss A C) p0000
  exact p0001

@[expose]
noncomputable def g_sstri (A : Class) (B : Class) (C : Class)
    (hyp_sstri_1 : Nominal.NPrf (syn_wss A B))
    (hyp_sstri_2 : Nominal.NPrf (syn_wss B C)) : Nominal.NPrf (syn_wss A C) :=
  by
  have p0000 := @g_sstr2 A B C
  have p0001 :=
    @g_mp2 (syn_wss A B) (syn_wss B C) (syn_wss A C) hyp_sstri_1 hyp_sstri_2 p0000
  exact p0001

@[expose]
noncomputable def g_sstrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sstrd_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_sstrd_2 : Nominal.NPrf (.imp ph (syn_wss B C))) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_sstr A B C
  have p0001 :=
    @g_syl2anc ph (syn_wss A B) (syn_wss B C) (syn_wss A C) hyp_sstrd_1 hyp_sstrd_2 p0000
  exact p0001

@[expose]
noncomputable def g_syl5ss (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5ss_1 : Nominal.NPrf (syn_wss A B))
    (hyp_syl5ss_2 : Nominal.NPrf (.imp ph (syn_wss B C))) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_a1i (syn_wss A B) ph hyp_syl5ss_1
  have p0001 := @g_sstrd ph A B C p0000 hyp_syl5ss_2
  exact p0001

@[expose]
noncomputable def g_syl6ss (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6ss_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_syl6ss_2 : Nominal.NPrf (syn_wss B C)) : Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_a1i (syn_wss B C) ph hyp_syl6ss_2
  have p0001 := @g_sstrd ph A B C hyp_syl6ss_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylan9ss (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sylan9ss_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_sylan9ss_2 : Nominal.NPrf (.imp ps (syn_wss B C))) :
    Nominal.NPrf (.imp (syn_wa ph ps) (syn_wss A C)) :=
  by
  have p0000 := @g_sstr A B C
  have p0001 :=
    @g_syl2an ph (syn_wss A B) (syn_wss B C) (syn_wss A C) ps hyp_sylan9ss_1
      hyp_sylan9ss_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq A B) (syn_wa (syn_wss A B) (syn_wss B A))) :=
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
  have p0000 := @g_albiim (.classMem (.cv x) A) (.classMem (.cv x) B) x
  have p0001 :=
    @g_dfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_dfss2 x B A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_anbi12i (syn_wss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wss B A) (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))) p0002
      p0003
  have p0005 :=
    @g_n_3bitr4i (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wa (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))))
      (.classEq A B) (syn_wa (syn_wss A B) (syn_wss B A)) p0000 p0001 p0004
  exact p0005

@[expose]
noncomputable def g_eqssi (A : Class) (B : Class)
    (hyp_eqssi_1 : Nominal.NPrf (syn_wss A B))
    (hyp_eqssi_2 : Nominal.NPrf (syn_wss B A)) : Nominal.NPrf (.classEq A B) :=
  by
  have p0000 := @g_eqss A B
  have p0001 :=
    @g_mpbir2an (.classEq A B) (syn_wss A B) (syn_wss B A) hyp_eqssi_1 hyp_eqssi_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqssd (ph : Wff) (A : Class) (B : Class)
    (hyp_eqssd_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_eqssd_2 : Nominal.NPrf (.imp ph (syn_wss B A))) :
    Nominal.NPrf (.imp ph (.classEq A B)) :=
  by
  have p0000 := @g_eqss A B
  have p0001 :=
    @g_sylanbrc ph (syn_wss A B) (syn_wss B A) (.classEq A B) hyp_eqssd_1 hyp_eqssd_2
      p0000
  exact p0001

@[expose]
noncomputable def g_ssid (A : Class) : Nominal.NPrf (syn_wss A A) :=
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
  have p0000 := @g_id (.classMem (.cv x) A)
  have p0001 :=
    @g_ssriv x A A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_ssv (A : Class) : Nominal.NPrf (syn_wss A (syn_cvv)) :=
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
  have p0000 := @g_elex (.cv x) A
  have p0001 :=
    @g_ssriv x A (syn_cvv)
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

@[expose]
noncomputable def g_sseq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wss A C) (syn_wss B C))) :=
  by
  have p0000 := @g_eqss A B
  have p0001 := @g_sstr2 B A C
  have p0002 :=
    @g_adantl (syn_wss B A) (.imp (syn_wss A C) (syn_wss B C)) (syn_wss A B) p0001
  have p0003 := @g_sstr2 A B C
  have p0004 :=
    @g_adantr (syn_wss A B) (.imp (syn_wss B C) (syn_wss A C)) (syn_wss B A) p0003
  have p0005 :=
    @g_impbid (syn_wa (syn_wss A B) (syn_wss B A)) (syn_wss A C) (syn_wss B C) p0002 p0004
  have p0006 :=
    @g_sylbi (.classEq A B) (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wb (syn_wss A C) (syn_wss B C)) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_sseq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wss C A) (syn_wss C B))) :=
  by
  have p0000 := @g_sstr2 C A B
  have p0001 := @g_com12 (syn_wss C A) (syn_wss A B) (syn_wss C B) p0000
  have p0002 := @g_sstr2 C B A
  have p0003 := @g_com12 (syn_wss C B) (syn_wss B A) (syn_wss C A) p0002
  have p0004 :=
    @g_anim12i (syn_wss A B) (.imp (syn_wss C A) (syn_wss C B)) (syn_wss B A)
      (.imp (syn_wss C B) (syn_wss C A)) p0001 p0003
  have p0005 := @g_eqss A B
  have p0006 := @g_dfbi2 (syn_wss C A) (syn_wss C B)
  have p0007 :=
    @g_n_3imtr4i (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (.imp (syn_wss C A) (syn_wss C B)) (.imp (syn_wss C B) (syn_wss C A)))
      (.classEq A B) (syn_wb (syn_wss C A) (syn_wss C B)) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_sseq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (syn_wb (syn_wss A C) (syn_wss B D))) :=
  by
  have p0000 := @g_sseq1 A B C
  have p0001 := @g_sseq2 C D B
  have p0002 :=
    @g_sylan9bb (.classEq A B) (syn_wss A C) (syn_wss B C) (.classEq C D) (syn_wss B D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sseq1i (A : Class) (B : Class) (C : Class)
    (hyp_sseq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wss A C) (syn_wss B C)) :=
  by
  have p0000 := @g_sseq1 A B C
  have p0001 := Nominal.mp hyp_sseq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_sseq2i (A : Class) (B : Class) (C : Class)
    (hyp_sseq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wss C A) (syn_wss C B)) :=
  by
  have p0000 := @g_sseq2 A B C
  have p0001 := Nominal.mp hyp_sseq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_sseq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_sseq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_sseq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (syn_wb (syn_wss A C) (syn_wss B D)) :=
  by
  have p0000 := @g_sseq12 A B C D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (syn_wb (syn_wss A C) (syn_wss B D))
      hyp_sseq1i_1 hyp_sseq12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_sseq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wss A C) (syn_wss B C))) :=
  by
  have p0000 := @g_sseq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wss A C) (syn_wss B C)) hyp_sseq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_sseq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wss C A) (syn_wss C B))) :=
  by
  have p0000 := @g_sseq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wss C A) (syn_wss C B)) hyp_sseq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_sseq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_sseq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_sseq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wss A C) (syn_wss B D))) :=
  by
  have p0000 := @g_sseq1d ph A B C hyp_sseq1d_1
  have p0001 := @g_sseq2d ph C D B hyp_sseq12d_2
  have p0002 := @g_bitrd ph (syn_wss A C) (syn_wss B C) (syn_wss B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqsstri (A : Class) (B : Class) (C : Class)
    (hyp_eqsstr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqsstr_2 : Nominal.NPrf (syn_wss B C)) : Nominal.NPrf (syn_wss A C) :=
  by
  have p0000 := @g_sseq1i A B C hyp_eqsstr_1
  have p0001 := @g_mpbir (syn_wss A C) (syn_wss B C) hyp_eqsstr_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqsstr3i (A : Class) (B : Class) (C : Class)
    (hyp_eqsstr3_1 : Nominal.NPrf (.classEq B A))
    (hyp_eqsstr3_2 : Nominal.NPrf (syn_wss B C)) : Nominal.NPrf (syn_wss A C) :=
  by
  have p0000 := @g_eqcomi B A hyp_eqsstr3_1
  have p0001 := @g_eqsstri A B C p0000 hyp_eqsstr3_2
  exact p0001

@[expose]
noncomputable def g_sseqtri (A : Class) (B : Class) (C : Class)
    (hyp_sseqtr_1 : Nominal.NPrf (syn_wss A B))
    (hyp_sseqtr_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (syn_wss A C) :=
  by
  have p0000 := @g_sseq2i B C A hyp_sseqtr_2
  have p0001 := @g_mpbi (syn_wss A B) (syn_wss A C) hyp_sseqtr_1 p0000
  exact p0001

@[expose]
noncomputable def g_sseqtr4i (A : Class) (B : Class) (C : Class)
    (hyp_sseqtr4_1 : Nominal.NPrf (syn_wss A B))
    (hyp_sseqtr4_2 : Nominal.NPrf (.classEq C B)) : Nominal.NPrf (syn_wss A C) :=
  by
  have p0000 := @g_eqcomi C B hyp_sseqtr4_2
  have p0001 := @g_sseqtri A B C hyp_sseqtr4_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqsstrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqsstrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqsstrd_2 : Nominal.NPrf (.imp ph (syn_wss B C))) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_sseq1d ph A B C hyp_eqsstrd_1
  have p0001 := @g_mpbird ph (syn_wss A C) (syn_wss B C) hyp_eqsstrd_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqsstr3d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqsstr3d_1 : Nominal.NPrf (.imp ph (.classEq B A)))
    (hyp_eqsstr3d_2 : Nominal.NPrf (.imp ph (syn_wss B C))) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_eqcomd ph B A hyp_eqsstr3d_1
  have p0001 := @g_eqsstrd ph A B C p0000 hyp_eqsstr3d_2
  exact p0001

@[expose]
noncomputable def g_sseqtrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseqtrd_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_sseqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_sseq2d ph B C A hyp_sseqtrd_2
  have p0001 := @g_mpbid ph (syn_wss A B) (syn_wss A C) hyp_sseqtrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_sseqtr4d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sseqtr4d_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_sseqtr4d_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_eqcomd ph C B hyp_sseqtr4d_2
  have p0001 := @g_sseqtrd ph A B C hyp_sseqtr4d_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3sstr4i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3sstr4_1 : Nominal.NPrf (syn_wss A B))
    (hyp_n_3sstr4_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3sstr4_3 : Nominal.NPrf (.classEq D B)) : Nominal.NPrf (syn_wss C D) :=
  by
  have p0000 := @g_sseq12i C A D B hyp_n_3sstr4_2 hyp_n_3sstr4_3
  have p0001 := @g_mpbir (syn_wss C D) (syn_wss A B) hyp_n_3sstr4_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3sstr4g (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3sstr4g_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_n_3sstr4g_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3sstr4g_3 : Nominal.NPrf (.classEq D B)) :
    Nominal.NPrf (.imp ph (syn_wss C D)) :=
  by
  have p0000 := @g_sseq12i C A D B hyp_n_3sstr4g_2 hyp_n_3sstr4g_3
  have p0001 := @g_sylibr ph (syn_wss A B) (syn_wss C D) hyp_n_3sstr4g_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3sstr4d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3sstr4d_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_n_3sstr4d_2 : Nominal.NPrf (.imp ph (.classEq C A)))
    (hyp_n_3sstr4d_3 : Nominal.NPrf (.imp ph (.classEq D B))) :
    Nominal.NPrf (.imp ph (syn_wss C D)) :=
  by
  have p0000 := @g_sseq12d ph C A D B hyp_n_3sstr4d_2 hyp_n_3sstr4d_3
  have p0001 := @g_mpbird ph (syn_wss C D) (syn_wss A B) hyp_n_3sstr4d_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5eqss (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqss_1 : Nominal.NPrf (.classEq A B))
    (hyp_syl5eqss_2 : Nominal.NPrf (.imp ph (syn_wss B C))) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_sseq1i A B C hyp_syl5eqss_1
  have p0001 := @g_sylibr ph (syn_wss B C) (syn_wss A C) hyp_syl5eqss_2 p0000
  exact p0001

@[expose]
noncomputable def g_syl5eqssr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqssr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5eqssr_2 : Nominal.NPrf (.imp ph (syn_wss B C))) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_eqcomi B A hyp_syl5eqssr_1
  have p0001 := @g_syl5eqss ph A B C p0000 hyp_syl5eqssr_2
  exact p0001

@[expose]
noncomputable def g_syl6sseq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6sseq_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_syl6sseq_2 : Nominal.NPrf (.classEq B C)) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_sseq2i B C A hyp_syl6sseq_2
  have p0001 := @g_sylib ph (syn_wss A B) (syn_wss A C) hyp_syl6sseq_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6sseqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6ssr_1 : Nominal.NPrf (.imp ph (syn_wss A B)))
    (hyp_syl6ssr_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_eqcomi C B hyp_syl6ssr_2
  have p0001 := @g_syl6sseq ph A B C hyp_syl6ssr_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5sseq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5sseq_1 : Nominal.NPrf (syn_wss B A))
    (hyp_syl5sseq_2 : Nominal.NPrf (.imp ph (.classEq A C))) :
    Nominal.NPrf (.imp ph (syn_wss B C)) :=
  by
  have p0000 := @g_sseq2 A C B
  have p0001 := @g_biimpa (.classEq A C) (syn_wss B A) (syn_wss B C) p0000
  have p0002 :=
    @g_sylancl ph (.classEq A C) (syn_wss B A) (syn_wss B C) hyp_syl5sseq_2 hyp_syl5sseq_1
      p0001
  exact p0002

@[expose]
noncomputable def g_syl5sseqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5sseqr_1 : Nominal.NPrf (syn_wss B A))
    (hyp_syl5sseqr_2 : Nominal.NPrf (.imp ph (.classEq C A))) :
    Nominal.NPrf (.imp ph (syn_wss B C)) :=
  by
  have p0000 := @g_a1i (syn_wss B A) ph hyp_syl5sseqr_1
  have p0001 := @g_sseqtr4d ph B A C p0000 hyp_syl5sseqr_2
  exact p0001

@[expose]
noncomputable def g_syl6eqss (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eqss_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eqss_2 : Nominal.NPrf (syn_wss B C)) :
    Nominal.NPrf (.imp ph (syn_wss A C)) :=
  by
  have p0000 := @g_a1i (syn_wss B C) ph hyp_syl6eqss_2
  have p0001 := @g_eqsstrd ph A B C hyp_syl6eqss_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqimss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wss A B)) :=
  by
  have p0000 := @g_eqss A B
  have p0001 := @g_simplbi (.classEq A B) (syn_wss A B) (syn_wss B A) p0000
  exact p0001

@[expose]
noncomputable def g_eqimss2 (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq B A) (syn_wss A B)) :=
  by
  have p0000 := @g_eqimss A B
  have p0001 := @g_eqcoms (syn_wss A B) A B p0000
  exact p0001

@[expose]
noncomputable def g_eqimssi (A : Class) (B : Class)
    (hyp_eqimssi_1 : Nominal.NPrf (.classEq A B)) : Nominal.NPrf (syn_wss A B) :=
  by
  have p0000 := @g_ssid A
  have p0001 := @g_sseqtri A A B p0000 hyp_eqimssi_1
  exact p0001

@[expose]
noncomputable def g_nss (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.neg (syn_wss A B))
        (syn_wex x (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_exanali (.classMem (.cv x) A) (.classMem (.cv x) B) x
  have p0001 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_xchbinxr (syn_wex x (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wss A B) p0000
      p0001
  have p0003 :=
    @g_bicomi (syn_wex x (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))
      (.neg (syn_wss A B)) p0002
  exact p0003

@[expose]
noncomputable def g_ss2ab (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wss (.cab x ph) (.cab x ps)) (.all x (.imp ph ps))) :=
  by
  have p0000 := @g_nfab1 ph x
  have p0001 := @g_nfab1 ps x
  have p0002 := @g_dfss2f x (.cab x ph) (.cab x ps) p0000 p0001
  have p0003 := @g_abid ph x
  have p0004 := @g_abid ps x
  have p0005 :=
    @g_imbi12i (.classMem (.cv x) (.cab x ph)) ph (.classMem (.cv x) (.cab x ps)) ps p0003
      p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) (.cab x ph)) (.classMem (.cv x) (.cab x ps)))
      (.imp ph ps) x p0005
  have p0007 :=
    @g_bitri (syn_wss (.cab x ph) (.cab x ps))
      (.all x (.imp (.classMem (.cv x) (.cab x ph)) (.classMem (.cv x) (.cab x ps))))
      (.all x (.imp ph ps)) p0002 p0006
  exact p0007

@[expose]
noncomputable def g_abss (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (syn_wss (.cab x ph) A) (.all x (.imp ph (.classMem (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_abid2 x A
      (by
        first
        | (aesop))
  have p0001 := @g_sseq2i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0000
  have p0002 := @g_ss2ab ph (.classMem (.cv x) A) x
  have p0003 :=
    @g_bitr3i (syn_wss (.cab x ph) A) (syn_wss (.cab x ph) (.cab x (.classMem (.cv x) A)))
      (.all x (.imp ph (.classMem (.cv x) A))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ssab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (syn_wss A (.cab x ph)) (.all x (.imp (.classMem (.cv x) A) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_abid2 x A
      (by
        first
        | (aesop))
  have p0001 := @g_sseq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0000
  have p0002 := @g_ss2ab (.classMem (.cv x) A) ph x
  have p0003 :=
    @g_bitr3i (syn_wss A (.cab x ph)) (syn_wss (.cab x (.classMem (.cv x) A)) (.cab x ph))
      (.all x (.imp (.classMem (.cv x) A) ph)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ss2abi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_ss2abi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (syn_wss (.cab x ph) (.cab x ps)) :=
  by
  have p0000 := @g_ss2ab ph ps x
  have p0001 :=
    @g_mpgbir (syn_wss (.cab x ph) (.cab x ps)) (.imp ph ps) x p0000 hyp_ss2abi_1
  exact p0001

@[expose]
noncomputable def g_ss2abdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_ss2abdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (syn_wss (.cab x ps) (.cab x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_alrimiv ph (.imp ps ch) x
      (by
        first
        | (aesop))
      hyp_ss2abdv_1
  have p0001 := @g_ss2ab ps ch x
  have p0002 :=
    @g_sylibr ph (.all x (.imp ps ch)) (syn_wss (.cab x ps) (.cab x ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_abssdv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_abssdv_1 : Nominal.NPrf (.imp ph (.imp ps (.classMem (.cv x) A)))) :
    Nominal.NPrf (.imp ph (syn_wss (.cab x ps) A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_alrimiv ph (.imp ps (.classMem (.cv x) A)) x
      (by
        first
        | (aesop))
      hyp_abssdv_1
  have p0001 :=
    @g_abss ps x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sylibr ph (.all x (.imp ps (.classMem (.cv x) A))) (syn_wss (.cab x ps) A) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_abssi (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_abssi_1 : Nominal.NPrf (.imp ph (.classMem (.cv x) A))) :
    Nominal.NPrf (syn_wss (.cab x ph) A) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_ss2abi ph (.classMem (.cv x) A) x hyp_abssi_1
  have p0001 :=
    @g_abid2 x A
      (by
        first
        | (aesop))
  have p0002 := @g_sseqtri (.cab x ph) (.cab x (.classMem (.cv x) A)) A p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ssab2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wss (.cab x (syn_wa (.classMem (.cv x) A) ph)) A) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_simpl (.classMem (.cv x) A) ph
  have p0001 :=
    @g_abssi (syn_wa (.classMem (.cv x) A) ph) x A
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_ssrab2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wss (syn_crab x A ph) A) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.classEqRefl (syn_crab x A ph))
  have p0001 :=
    @g_ssab2 ph x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_eqsstri (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph)) A p0000 p0001
  exact p0002

@[expose]
noncomputable def g_dfpss2 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wpss A B) (syn_wa (syn_wss A B) (.neg (.classEq A B)))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wpss A B))
  have p0001 := (Nominal.biimpRefl (syn_wne A B))
  have p0002 := @g_anbi2i (syn_wne A B) (.neg (.classEq A B)) (syn_wss A B) p0001
  have p0003 :=
    @g_bitri (syn_wpss A B) (syn_wa (syn_wss A B) (syn_wne A B))
      (syn_wa (syn_wss A B) (.neg (.classEq A B))) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_dfpss3 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wpss A B) (syn_wa (syn_wss A B) (.neg (syn_wss B A)))) :=
  by
  have p0000 := @g_dfpss2 A B
  have p0001 := @g_eqss A B
  have p0002 := @g_baib (.classEq A B) (syn_wss A B) (syn_wss B A) p0001
  have p0003 := @g_notbid (syn_wss A B) (.classEq A B) (syn_wss B A) p0002
  have p0004 := @g_pm5_32i (syn_wss A B) (.neg (.classEq A B)) (.neg (syn_wss B A)) p0003
  have p0005 :=
    @g_bitri (syn_wpss A B) (syn_wa (syn_wss A B) (.neg (.classEq A B)))
      (syn_wa (syn_wss A B) (.neg (syn_wss B A))) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_pssss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wpss A B) (syn_wss A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wpss A B))
  have p0001 := @g_simplbi (syn_wpss A B) (syn_wss A B) (syn_wne A B) p0000
  exact p0001

@[expose]
noncomputable def g_pssssd (ph : Wff) (A : Class) (B : Class)
    (hyp_pssssd_1 : Nominal.NPrf (.imp ph (syn_wpss A B))) :
    Nominal.NPrf (.imp ph (syn_wss A B)) :=
  by
  have p0000 := @g_pssss A B
  have p0001 := @g_syl ph (syn_wpss A B) (syn_wss A B) hyp_pssssd_1 p0000
  exact p0001

@[expose]
noncomputable def g_sspss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (syn_wo (syn_wpss A B) (.classEq A B))) :=
  by
  have p0000 := @g_dfpss2 A B
  have p0001 := @g_simplbi2 (syn_wpss A B) (syn_wss A B) (.neg (.classEq A B)) p0000
  have p0002 := @g_con1d (syn_wss A B) (.classEq A B) (syn_wpss A B) p0001
  have p0003 := @g_orrd (syn_wss A B) (syn_wpss A B) (.classEq A B) p0002
  have p0004 := @g_pssss A B
  have p0005 := @g_eqimss A B
  have p0006 := @g_jaoi (syn_wpss A B) (syn_wss A B) (.classEq A B) p0004 p0005
  have p0007 := @g_impbii (syn_wss A B) (syn_wo (syn_wpss A B) (.classEq A B)) p0003 p0006
  exact p0007

@[expose]
noncomputable def g_difeq1i (A : Class) (B : Class) (C : Class)
    (hyp_difeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cdif A C) (syn_cdif B C)) :=
  by
  have p0000 := @g_difeq1 A B C
  have p0001 := Nominal.mp hyp_difeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_difeq2i (A : Class) (B : Class) (C : Class)
    (hyp_difeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cdif C A) (syn_cdif C B)) :=
  by
  have p0000 := @g_difeq2 A B C
  have p0001 := Nominal.mp hyp_difeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_difeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_difeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cdif A C) (syn_cdif B C))) :=
  by
  have p0000 := @g_difeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cdif A C) (syn_cdif B C)) hyp_difeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_difeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_difeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cdif C A) (syn_cdif C B))) :=
  by
  have p0000 := @g_difeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cdif C A) (syn_cdif C B)) hyp_difeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_difeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_difeq12d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_difeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cdif A C) (syn_cdif B D))) :=
  by
  have p0000 := @g_difeq1d ph A B C hyp_difeq12d_1
  have p0001 := @g_difeq2d ph C D B hyp_difeq12d_2
  have p0002 := @g_eqtrd ph (syn_cdif A C) (syn_cdif B C) (syn_cdif B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_difeqri (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (hyp_difeqri_1 : Nominal.NPrf
        (syn_wb (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
          (.classMem (.cv x) C))) :
    Nominal.NPrf (.classEq (syn_cdif A B) C) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @g_eldif (.cv x) A B
  have p0001 :=
    @g_bitri (.classMem (.cv x) (syn_cdif A B))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) C)
      p0000 hyp_difeqri_1
  have p0002 :=
    @g_eqriv x (syn_cdif A B) C
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

@[expose]
noncomputable def g_eldifi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cdif B C)) (.classMem A B)) :=
  by
  have p0000 := @g_eldif A B C
  have p0001 :=
    @g_simplbi (.classMem A (syn_cdif B C)) (.classMem A B) (.neg (.classMem A C)) p0000
  exact p0001

@[expose]
noncomputable def g_eldifn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cdif B C)) (.neg (.classMem A C))) :=
  by
  have p0000 := @g_eldif A B C
  have p0001 :=
    @g_simprbi (.classMem A (syn_cdif B C)) (.classMem A B) (.neg (.classMem A C)) p0000
  exact p0001

@[expose]
noncomputable def g_difdif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cdif A (syn_cdif B A)) A) :=
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
  have p0000 := @g_pm4_45im (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @g_iman (.classMem (.cv x) B) (.classMem (.cv x) A)
  have p0002 := @g_eldif (.cv x) B A
  have p0003 :=
    @g_xchbinxr (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))
      (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A)))
      (.classMem (.cv x) (syn_cdif B A)) p0001 p0002
  have p0004 :=
    @g_anbi2i (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.neg (.classMem (.cv x) (syn_cdif B A))) (.classMem (.cv x) A) p0003
  have p0005 :=
    @g_bitr2i (.classMem (.cv x) A)
      (syn_wa (.classMem (.cv x) A) (.imp (.classMem (.cv x) B) (.classMem (.cv x) A)))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_cdif B A)))) p0000 p0004
  have p0006 :=
    @g_difeqri x A (syn_cdif B A) A
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

@[expose]
noncomputable def g_difss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cdif A B) A) :=
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
  have p0000 := @g_eldifi (.cv x) A B
  have p0001 :=
    @g_ssriv x (syn_cdif A B) A
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

@[expose]
noncomputable def g_ddif (A : Class) :
    Nominal.NPrf (.classEq (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) A)) A) :=
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
  have p0000 := @g_vex x
  have p0001 := @g_eldif (.cv x) (syn_cvv) A
  have p0002 :=
    @g_mpbiran (.classMem (.cv x) (syn_cdif (syn_cvv) A)) (.classMem (.cv x) (syn_cvv))
      (.neg (.classMem (.cv x) A)) p0000 p0001
  have p0003 :=
    @g_con2bii (.classMem (.cv x) (syn_cdif (syn_cvv) A)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_biantrur (.classMem (.cv x) (syn_cvv))
      (.neg (.classMem (.cv x) (syn_cdif (syn_cvv) A))) p0000
  have p0005 :=
    @g_bitr2i (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_cdif (syn_cvv) A)))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg (.classMem (.cv x) (syn_cdif (syn_cvv) A))))
      p0003 p0004
  have p0006 :=
    @g_difeqri x (syn_cvv) (syn_cdif (syn_cvv) A) A
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

@[expose]
noncomputable def g_ssdif (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cdif A C) (syn_cdif B C))) :=
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
  have p0000 := @g_ssel A B (.cv x)
  have p0001 :=
    @g_anim1d (syn_wss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.neg (.classMem (.cv x) C)) p0000
  have p0002 := @g_eldif (.cv x) A C
  have p0003 := @g_eldif (.cv x) B C
  have p0004 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) C)))
      (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) C)))
      (.classMem (.cv x) (syn_cdif A C)) (.classMem (.cv x) (syn_cdif B C)) p0001 p0002
      p0003
  have p0005 :=
    @g_ssrdv (syn_wss A B) x (syn_cdif A C) (syn_cdif B C)
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

@[expose]
noncomputable def g_uneqri (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (hyp_uneqri_1 : Nominal.NPrf (syn_wb (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
          (.classMem (.cv x) C))) :
    Nominal.NPrf (.classEq (syn_cun A B) C) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @g_elun (.cv x) A B
  have p0001 :=
    @g_bitri (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0000
      hyp_uneqri_1
  have p0002 :=
    @g_eqriv x (syn_cun A B) C
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

@[expose]
noncomputable def g_unidm (A : Class) : Nominal.NPrf (.classEq (syn_cun A A) A) :=
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
  have p0000 := @g_oridm (.classMem (.cv x) A)
  have p0001 :=
    @g_uneqri x A A A
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
noncomputable def g_uncom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cun A B) (syn_cun B A)) :=
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
  have p0000 := @g_orcom (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @g_elun (.cv x) B A
  have p0002 :=
    @g_bitr4i (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.classMem (.cv x) (syn_cun B A)) p0000 p0001
  have p0003 :=
    @g_uneqri x A B (syn_cun B A)
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

@[expose]
noncomputable def g_uneq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cun A C) (syn_cun B C))) :=
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
  have p0000 := @g_eleq2 A B (.cv x)
  have p0001 :=
    @g_orbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 := @g_elun (.cv x) A C
  have p0003 := @g_elun (.cv x) B C
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) C))
      (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.classMem (.cv x) (syn_cun A C)) (.classMem (.cv x) (syn_cun B C)) p0001 p0002
      p0003
  have p0005 :=
    @g_eqrdv (.classEq A B) x (syn_cun A C) (syn_cun B C)
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

@[expose]
noncomputable def g_uneq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cun C A) (syn_cun C B))) :=
  by
  have p0000 := @g_uneq1 A B C
  have p0001 := @g_uncom C A
  have p0002 := @g_uncom C B
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cun A C) (syn_cun B C) (syn_cun C A) (syn_cun C B)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_uneq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (.classEq (syn_cun A C) (syn_cun B D))) :=
  by
  have p0000 := @g_uneq1 A B C
  have p0001 := @g_uneq2 C D B
  have p0002 :=
    @g_sylan9eq (.classEq A B) (.classEq C D) (syn_cun A C) (syn_cun B C) (syn_cun B D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_uneq1i (A : Class) (B : Class) (C : Class)
    (hyp_uneq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cun A C) (syn_cun B C)) :=
  by
  have p0000 := @g_uneq1 A B C
  have p0001 := Nominal.mp hyp_uneq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_uneq2i (A : Class) (B : Class) (C : Class)
    (hyp_uneq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cun C A) (syn_cun C B)) :=
  by
  have p0000 := @g_uneq2 A B C
  have p0001 := Nominal.mp hyp_uneq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_uneq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_uneq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_uneq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cun A C) (syn_cun B D)) :=
  by
  have p0000 := @g_uneq12 A B C D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (.classEq (syn_cun A C) (syn_cun B D))
      hyp_uneq1i_1 hyp_uneq12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_uneq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_uneq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cun A C) (syn_cun B C))) :=
  by
  have p0000 := @g_uneq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cun A C) (syn_cun B C)) hyp_uneq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_uneq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_uneq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cun C A) (syn_cun C B))) :=
  by
  have p0000 := @g_uneq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cun C A) (syn_cun C B)) hyp_uneq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_uneq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_uneq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_uneq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cun A C) (syn_cun B D))) :=
  by
  have p0000 := @g_uneq12 A B C D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_cun A C) (syn_cun B D))
      hyp_uneq1d_1 hyp_uneq12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_unass (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cun (syn_cun A B) C) (syn_cun A (syn_cun B C))) :=
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
  have p0000 := @g_elun (.cv x) A (syn_cun B C)
  have p0001 := @g_elun (.cv x) B C
  have p0002 :=
    @g_orbi2i (.classMem (.cv x) (syn_cun B C))
      (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0001
  have p0003 := @g_elun (.cv x) A B
  have p0004 :=
    @g_orbi1i (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0003
  have p0005 := @g_orass (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0006 :=
    @g_bitr2i (syn_wo (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) C))
      (syn_wo (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (syn_wo (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      p0004 p0005
  have p0007 :=
    @g_n_3bitrri (.classMem (.cv x) (syn_cun A (syn_cun B C)))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) (syn_cun B C)))
      (syn_wo (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (syn_wo (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) C)) p0000 p0002 p0006
  have p0008 :=
    @g_uneqri x (syn_cun A B) C (syn_cun A (syn_cun B C))
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

@[expose]
noncomputable def g_ssun1 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss A (syn_cun A B)) :=
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
  have p0000 := @g_orc (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @g_elun (.cv x) A B
  have p0002 :=
    @g_sylibr (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classMem (.cv x) (syn_cun A B)) p0000 p0001
  have p0003 :=
    @g_ssriv x A (syn_cun A B)
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

@[expose]
noncomputable def g_ssun2 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss A (syn_cun B A)) :=
  by
  have p0000 := @g_ssun1 A B
  have p0001 := @g_uncom A B
  have p0002 := @g_sseqtri A (syn_cun A B) (syn_cun B A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ssun3 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss A (syn_cun B C))) :=
  by
  have p0000 := @g_ssun1 B C
  have p0001 := @g_sstr2 A B (syn_cun B C)
  have p0002 :=
    @g_mpi (syn_wss A B) (syn_wss B (syn_cun B C)) (syn_wss A (syn_cun B C)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elun1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem A (syn_cun B C))) :=
  by
  have p0000 := @g_ssun1 B C
  have p0001 := @g_sseli B (syn_cun B C) A p0000
  exact p0001

@[expose]
noncomputable def g_elun2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem A (syn_cun C B))) :=
  by
  have p0000 := @g_ssun2 B C
  have p0001 := @g_sseli B (syn_cun C B) A p0000
  exact p0001

@[expose]
noncomputable def g_unss1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cun A C) (syn_cun B C))) :=
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
  have p0000 := @g_ssel A B (.cv x)
  have p0001 :=
    @g_orim1d (syn_wss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 := @g_elun (.cv x) A C
  have p0003 := @g_elun (.cv x) B C
  have p0004 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) C))
      (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.classMem (.cv x) (syn_cun A C)) (.classMem (.cv x) (syn_cun B C)) p0001 p0002
      p0003
  have p0005 :=
    @g_ssrdv (syn_wss A B) x (syn_cun A C) (syn_cun B C)
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

@[expose]
noncomputable def g_ssequn1 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cun A B) B)) :=
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
    @g_bicom (.classMem (.cv x) B) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
  have p0001 := @g_pm4_72 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0002 := @g_elun (.cv x) A B
  have p0003 :=
    @g_bibi1i (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) B) p0002
  have p0004 :=
    @g_n_3bitr4i
      (syn_wb (.classMem (.cv x) B) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wb (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) B)) p0000 p0001 p0003
  have p0005 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) B)) x p0004
  have p0006 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0007 :=
    @g_dfcleq x (syn_cun A B) B
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
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (syn_wb (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) B)))
      (syn_wss A B) (.classEq (syn_cun A B) B) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_unss2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cun C A) (syn_cun C B))) :=
  by
  have p0000 := @g_unss1 A B C
  have p0001 := @g_uncom C A
  have p0002 := @g_uncom C B
  have p0003 :=
    @g_n_3sstr4g (syn_wss A B) (syn_cun A C) (syn_cun B C) (syn_cun C A) (syn_cun C B)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_unss12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wss A B) (syn_wss C D)) (syn_wss (syn_cun A C) (syn_cun B D))) :=
  by
  have p0000 := @g_unss1 A B C
  have p0001 := @g_unss2 C D B
  have p0002 :=
    @g_sylan9ss (syn_wss A B) (syn_wss C D) (syn_cun A C) (syn_cun B C) (syn_cun B D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ssequn2 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cun B A) B)) :=
  by
  have p0000 := @g_ssequn1 A B
  have p0001 := @g_uncom A B
  have p0002 := @g_eqeq1i (syn_cun A B) (syn_cun B A) B p0001
  have p0003 :=
    @g_bitri (syn_wss A B) (.classEq (syn_cun A B) B) (.classEq (syn_cun B A) B) p0000
      p0002
  exact p0003

@[expose]
noncomputable def g_unss (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_wss A C) (syn_wss B C)) (syn_wss (syn_cun A B) C)) :=
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
    @g_dfss2 x (syn_cun A B) C
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
    @g_n_19_26 (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))
      (.imp (.classMem (.cv x) B) (.classMem (.cv x) C)) x
  have p0002 := @g_elun (.cv x) A B
  have p0003 :=
    @g_imbi1i (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0002
  have p0004 := @g_jaob (.classMem (.cv x) A) (.classMem (.cv x) C) (.classMem (.cv x) B)
  have p0005 :=
    @g_bitri (.imp (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) C))
      (.imp (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (syn_wa (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))
        (.imp (.classMem (.cv x) B) (.classMem (.cv x) C)))
      p0003 p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) C))
      (syn_wa (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))
        (.imp (.classMem (.cv x) B) (.classMem (.cv x) C)))
      x p0005
  have p0007 :=
    @g_dfss2 x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @g_dfss2 x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0009 :=
    @g_anbi12i (syn_wss A C) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (syn_wss B C) (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) C))) p0007
      p0008
  have p0010 :=
    @g_n_3bitr4i
      (.all x (syn_wa (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))
          (.imp (.classMem (.cv x) B) (.classMem (.cv x) C))))
      (syn_wa (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)))
        (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv x) C))))
      (.all x (.imp (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) C)))
      (syn_wa (syn_wss A C) (syn_wss B C)) p0001 p0006 p0009
  have p0011 :=
    @g_bitr2i (syn_wss (syn_cun A B) C)
      (.all x (.imp (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) C)))
      (syn_wa (syn_wss A C) (syn_wss B C)) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_unssi (A : Class) (B : Class) (C : Class)
    (hyp_unssi_1 : Nominal.NPrf (syn_wss A C))
    (hyp_unssi_2 : Nominal.NPrf (syn_wss B C)) : Nominal.NPrf (syn_wss (syn_cun A B) C) :=
  by
  have p0000 := @g_pm3_2i (syn_wss A C) (syn_wss B C) hyp_unssi_1 hyp_unssi_2
  have p0001 := @g_unss A B C
  have p0002 :=
    @g_mpbi (syn_wa (syn_wss A C) (syn_wss B C)) (syn_wss (syn_cun A B) C) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_unssd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_unssd_1 : Nominal.NPrf (.imp ph (syn_wss A C)))
    (hyp_unssd_2 : Nominal.NPrf (.imp ph (syn_wss B C))) :
    Nominal.NPrf (.imp ph (syn_wss (syn_cun A B) C)) :=
  by
  have p0000 := @g_unss A B C
  have p0001 :=
    @g_biimpi (syn_wa (syn_wss A C) (syn_wss B C)) (syn_wss (syn_cun A B) C) p0000
  have p0002 :=
    @g_syl2anc ph (syn_wss A C) (syn_wss B C) (syn_wss (syn_cun A B) C) hyp_unssd_1
      hyp_unssd_2 p0001
  exact p0002

@[expose]
noncomputable def g_rexun (ph : Wff) (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (syn_wrex x (syn_cun A B) ph) (syn_wo (syn_wrex x A ph) (syn_wrex x B ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wrex x (syn_cun A B) ph))
  have p0001 :=
    @g_n_19_43 (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) ph) x
  have p0002 := @g_elun (.cv x) A B
  have p0003 :=
    @g_anbi1i (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) ph p0002
  have p0004 := @g_andir (.classMem (.cv x) A) (.classMem (.cv x) B) ph
  have p0005 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_cun A B)) ph)
      (syn_wa (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) ph)
      (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) ph)) p0003
      p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv x) (syn_cun A B)) ph)
      (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) ph)) x p0005
  have p0007 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0008 := (Nominal.biimpRefl (syn_wrex x B ph))
  have p0009 :=
    @g_orbi12i (syn_wrex x A ph) (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wrex x B ph) (syn_wex x (syn_wa (.classMem (.cv x) B) ph)) p0007 p0008
  have p0010 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) ph)))
      (syn_wo (syn_wex x (syn_wa (.classMem (.cv x) A) ph))
        (syn_wex x (syn_wa (.classMem (.cv x) B) ph)))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_cun A B)) ph))
      (syn_wo (syn_wrex x A ph) (syn_wrex x B ph)) p0001 p0006 p0009
  have p0011 :=
    @g_bitri (syn_wrex x (syn_cun A B) ph)
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_cun A B)) ph))
      (syn_wo (syn_wrex x A ph) (syn_wrex x B ph)) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_ralunb (ph : Wff) (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (syn_wral x (syn_cun A B) ph) (syn_wa (syn_wral x A ph) (syn_wral x B ph))) :=
  by
  have p0000 := @g_elun (.cv x) A B
  have p0001 :=
    @g_imbi1i (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) ph p0000
  have p0002 := @g_jaob (.classMem (.cv x) A) ph (.classMem (.cv x) B)
  have p0003 :=
    @g_bitri (.imp (.classMem (.cv x) (syn_cun A B)) ph)
      (.imp (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) ph)
      (syn_wa (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ph)) p0001 p0002
  have p0004 :=
    @g_albii (.imp (.classMem (.cv x) (syn_cun A B)) ph)
      (syn_wa (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ph)) x p0003
  have p0005 :=
    @g_n_19_26 (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ph) x
  have p0006 :=
    @g_bitri (.all x (.imp (.classMem (.cv x) (syn_cun A B)) ph))
      (.all x (syn_wa (.imp (.classMem (.cv x) A) ph) (.imp (.classMem (.cv x) B) ph)))
      (syn_wa (.all x (.imp (.classMem (.cv x) A) ph)) (.all x (.imp (.classMem (.cv x) B) ph)))
      p0004 p0005
  have p0007 := (Nominal.biimpRefl (syn_wral x (syn_cun A B) ph))
  have p0008 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0009 := (Nominal.biimpRefl (syn_wral x B ph))
  have p0010 :=
    @g_anbi12i (syn_wral x A ph) (.all x (.imp (.classMem (.cv x) A) ph))
      (syn_wral x B ph) (.all x (.imp (.classMem (.cv x) B) ph)) p0008 p0009
  have p0011 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) (syn_cun A B)) ph))
      (syn_wa (.all x (.imp (.classMem (.cv x) A) ph)) (.all x (.imp (.classMem (.cv x) B) ph)))
      (syn_wral x (syn_cun A B) ph) (syn_wa (syn_wral x A ph) (syn_wral x B ph)) p0006
      p0007 p0010
  exact p0011

@[expose]
noncomputable def g_elin2 (A : Class) (B : Class) (C : Class) (X : Class)
    (hyp_elin2_x : Nominal.NPrf (.classEq X (syn_cin B C))) :
    Nominal.NPrf (syn_wb (.classMem A X) (syn_wa (.classMem A B) (.classMem A C))) :=
  by
  have p0000 := @g_eleq2i X (syn_cin B C) A hyp_elin2_x
  have p0001 := @g_elin A B C
  have p0002 :=
    @g_bitri (.classMem A X) (.classMem A (syn_cin B C))
      (syn_wa (.classMem A B) (.classMem A C)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_incom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin A B) (syn_cin B A)) :=
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
  have p0000 := @g_ancom (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @g_elin (.cv x) A B
  have p0002 := @g_elin (.cv x) B A
  have p0003 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) (syn_cin B A)) p0000 p0001
      p0002
  have p0004 :=
    @g_eqriv x (syn_cin A B) (syn_cin B A)
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

@[expose]
noncomputable def g_ineqri (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (hyp_ineqri_1 : Nominal.NPrf (syn_wb (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
          (.classMem (.cv x) C))) :
    Nominal.NPrf (.classEq (syn_cin A B) C) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @g_elin (.cv x) A B
  have p0001 :=
    @g_bitri (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0000
      hyp_ineqri_1
  have p0002 :=
    @g_eqriv x (syn_cin A B) C
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

@[expose]
noncomputable def g_ineq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cin A C) (syn_cin B C))) :=
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
  have p0000 := @g_eleq2 A B (.cv x)
  have p0001 :=
    @g_anbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 := @g_elin (.cv x) A C
  have p0003 := @g_elin (.cv x) B C
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv x) (syn_cin B C)) p0001 p0002
      p0003
  have p0005 :=
    @g_eqrdv (.classEq A B) x (syn_cin A C) (syn_cin B C)
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

@[expose]
noncomputable def g_ineq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cin C A) (syn_cin C B))) :=
  by
  have p0000 := @g_ineq1 A B C
  have p0001 := @g_incom C A
  have p0002 := @g_incom C B
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cin A C) (syn_cin B C) (syn_cin C A) (syn_cin C B)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ineq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (.classEq (syn_cin A C) (syn_cin B D))) :=
  by
  have p0000 := @g_ineq1 A B C
  have p0001 := @g_ineq2 C D B
  have p0002 :=
    @g_sylan9eq (.classEq A B) (.classEq C D) (syn_cin A C) (syn_cin B C) (syn_cin B D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ineq1i (A : Class) (B : Class) (C : Class)
    (hyp_ineq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cin A C) (syn_cin B C)) :=
  by
  have p0000 := @g_ineq1 A B C
  have p0001 := Nominal.mp hyp_ineq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_ineq2i (A : Class) (B : Class) (C : Class)
    (hyp_ineq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cin C A) (syn_cin C B)) :=
  by
  have p0000 := @g_ineq2 A B C
  have p0001 := Nominal.mp hyp_ineq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_ineq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_ineq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_ineq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cin A C) (syn_cin B D)) :=
  by
  have p0000 := @g_ineq12 A B C D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (.classEq (syn_cin A C) (syn_cin B D))
      hyp_ineq1i_1 hyp_ineq12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_ineq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ineq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cin A C) (syn_cin B C))) :=
  by
  have p0000 := @g_ineq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cin A C) (syn_cin B C)) hyp_ineq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_ineq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ineq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cin C A) (syn_cin C B))) :=
  by
  have p0000 := @g_ineq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cin C A) (syn_cin C B)) hyp_ineq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_ineq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_ineq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_ineq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cin A C) (syn_cin B D))) :=
  by
  have p0000 := @g_ineq12 A B C D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_cin A C) (syn_cin B D))
      hyp_ineq1d_1 hyp_ineq12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_dfss1 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cin B A) A)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wss A B))
  have p0001 := @g_incom A B
  have p0002 := @g_eqeq1i (syn_cin A B) (syn_cin B A) A p0001
  have p0003 :=
    @g_bitri (syn_wss A B) (.classEq (syn_cin A B) A) (.classEq (syn_cin B A) A) p0000
      p0002
  exact p0003

@[expose]
noncomputable def g_inidm (A : Class) : Nominal.NPrf (.classEq (syn_cin A A) A) :=
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
  have p0000 := @g_anidm (.classMem (.cv x) A)
  have p0001 :=
    @g_ineqri x A A A
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
noncomputable def g_inass (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cin (syn_cin A B) C) (syn_cin A (syn_cin B C))) :=
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
  have p0000 := @g_anass (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0001 := @g_elin (.cv x) B C
  have p0002 :=
    @g_anbi2i (.classMem (.cv x) (syn_cin B C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0001
  have p0003 :=
    @g_bitr4i
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin B C))) p0000 p0002
  have p0004 := @g_elin (.cv x) A B
  have p0005 :=
    @g_anbi1i (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0004
  have p0006 := @g_elin (.cv x) A (syn_cin B C)
  have p0007 :=
    @g_n_3bitr4i
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin B C)))
      (syn_wa (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C))
      (.classMem (.cv x) (syn_cin A (syn_cin B C))) p0003 p0005 p0006
  have p0008 :=
    @g_ineqri x (syn_cin A B) C (syn_cin A (syn_cin B C))
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

@[expose]
noncomputable def g_in12 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_cin B C)) (syn_cin B (syn_cin A C))) :=
  by
  have p0000 := @g_incom A B
  have p0001 := @g_ineq1i (syn_cin A B) (syn_cin B A) C p0000
  have p0002 := @g_inass A B C
  have p0003 := @g_inass B A C
  have p0004 :=
    @g_n_3eqtr3i (syn_cin (syn_cin A B) C) (syn_cin (syn_cin B A) C)
      (syn_cin A (syn_cin B C)) (syn_cin B (syn_cin A C)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_in32 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cin (syn_cin A B) C) (syn_cin (syn_cin A C) B)) :=
  by
  have p0000 := @g_inass A B C
  have p0001 := @g_in12 A B C
  have p0002 := @g_incom B (syn_cin A C)
  have p0003 :=
    @g_n_3eqtri (syn_cin (syn_cin A B) C) (syn_cin A (syn_cin B C))
      (syn_cin B (syn_cin A C)) (syn_cin (syn_cin A C) B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_in4 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.classEq (syn_cin (syn_cin A B) (syn_cin C D)) (syn_cin (syn_cin A C) (syn_cin B D))) :=
  by
  have p0000 := @g_in12 B C D
  have p0001 := @g_ineq2i (syn_cin B (syn_cin C D)) (syn_cin C (syn_cin B D)) A p0000
  have p0002 := @g_inass A B (syn_cin C D)
  have p0003 := @g_inass A C (syn_cin B D)
  have p0004 :=
    @g_n_3eqtr4i (syn_cin A (syn_cin B (syn_cin C D)))
      (syn_cin A (syn_cin C (syn_cin B D))) (syn_cin (syn_cin A B) (syn_cin C D))
      (syn_cin (syn_cin A C) (syn_cin B D)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_inindi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cin A (syn_cin B C)) (syn_cin (syn_cin A B) (syn_cin A C))) :=
  by
  have p0000 := @g_inidm A
  have p0001 := @g_ineq1i (syn_cin A A) A (syn_cin B C) p0000
  have p0002 := @g_in4 A A B C
  have p0003 :=
    @g_eqtr3i (syn_cin (syn_cin A A) (syn_cin B C)) (syn_cin A (syn_cin B C))
      (syn_cin (syn_cin A B) (syn_cin A C)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_sseqin2 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cin B A) A)) :=
  by
  have p0000 := @g_dfss1 A B
  exact p0000

@[expose]
noncomputable def g_inss1 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cin A B) A) :=
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
  have p0000 := @g_elin (.cv x) A B
  have p0001 :=
    @g_simplbi (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) A)
      (.classMem (.cv x) B) p0000
  have p0002 :=
    @g_ssriv x (syn_cin A B) A
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

@[expose]
noncomputable def g_inss2 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cin A B) B) :=
  by
  have p0000 := @g_incom B A
  have p0001 := @g_inss1 B A
  have p0002 := @g_eqsstr3i (syn_cin A B) (syn_cin B A) B p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ssin (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_wss A B) (syn_wss A C)) (syn_wss A (syn_cin B C))) :=
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
  have p0000 := @g_elin (.cv x) B C
  have p0001 :=
    @g_imbi2i (.classMem (.cv x) (syn_cin B C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin B C)))
      (.imp (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C))) x
      p0001
  have p0003 := @g_jcab (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0004 :=
    @g_albii
      (.imp (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (syn_wa (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
        (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)))
      x p0003
  have p0005 :=
    @g_n_19_26 (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) C)) x
  have p0006 :=
    @g_n_3bitrri (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin B C))))
      (.all x (.imp (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C))))
      (.all x (syn_wa (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
          (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))))
      (syn_wa (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))))
      p0002 p0004 p0005
  have p0007 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @g_dfss2 x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0009 :=
    @g_anbi12i (syn_wss A B) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wss A C) (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))) p0007
      p0008
  have p0010 :=
    @g_dfss2 x A (syn_cin B C)
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
    @g_n_3bitr4i
      (syn_wa (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) C))))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin B C))))
      (syn_wa (syn_wss A B) (syn_wss A C)) (syn_wss A (syn_cin B C)) p0006 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_ssini (A : Class) (B : Class) (C : Class)
    (hyp_ssini_1 : Nominal.NPrf (syn_wss A B))
    (hyp_ssini_2 : Nominal.NPrf (syn_wss A C)) : Nominal.NPrf (syn_wss A (syn_cin B C)) :=
  by
  have p0000 := @g_pm3_2i (syn_wss A B) (syn_wss A C) hyp_ssini_1 hyp_ssini_2
  have p0001 := @g_ssin A B C
  have p0002 :=
    @g_mpbi (syn_wa (syn_wss A B) (syn_wss A C)) (syn_wss A (syn_cin B C)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ssrin (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cin A C) (syn_cin B C))) :=
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
  have p0000 := @g_ssel A B (.cv x)
  have p0001 :=
    @g_anim1d (syn_wss A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 := @g_elin (.cv x) A C
  have p0003 := @g_elin (.cv x) B C
  have p0004 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C))
      (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv x) (syn_cin B C)) p0001 p0002
      p0003
  have p0005 :=
    @g_ssrdv (syn_wss A B) x (syn_cin A C) (syn_cin B C)
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

@[expose]
noncomputable def g_sslin (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cin C A) (syn_cin C B))) :=
  by
  have p0000 := @g_ssrin A B C
  have p0001 := @g_incom C A
  have p0002 := @g_incom C B
  have p0003 :=
    @g_n_3sstr4g (syn_wss A B) (syn_cin A C) (syn_cin B C) (syn_cin C A) (syn_cin C B)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_dfss4 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cdif B (syn_cdif B A)) A)) :=
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
  have p0000 := @g_sseqin2 A B
  have p0001 := @g_eldif (.cv x) B A
  have p0002 :=
    @g_notbii (.classMem (.cv x) (syn_cdif B A))
      (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A))) p0001
  have p0003 :=
    @g_anbi2i (.neg (.classMem (.cv x) (syn_cdif B A)))
      (.neg (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A))))
      (.classMem (.cv x) B) p0002
  have p0004 := @g_elin (.cv x) B A
  have p0005 := @g_abai (.classMem (.cv x) B) (.classMem (.cv x) A)
  have p0006 := @g_iman (.classMem (.cv x) B) (.classMem (.cv x) A)
  have p0007 :=
    @g_anbi2i (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))
      (.neg (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A))))
      (.classMem (.cv x) B) p0006
  have p0008 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cin B A))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) A))
      (syn_wa (.classMem (.cv x) B) (.imp (.classMem (.cv x) B) (.classMem (.cv x) A)))
      (syn_wa (.classMem (.cv x) B)
        (.neg (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A)))))
      p0004 p0005 p0007
  have p0009 :=
    @g_bitr4i (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) (syn_cdif B A))))
      (syn_wa (.classMem (.cv x) B)
        (.neg (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) A)))))
      (.classMem (.cv x) (syn_cin B A)) p0003 p0008
  have p0010 :=
    @g_difeqri x B (syn_cdif B A) (syn_cin B A)
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
  have p0011 := @g_eqeq1i (syn_cdif B (syn_cdif B A)) (syn_cin B A) A p0010
  have p0012 :=
    @g_bitr4i (syn_wss A B) (.classEq (syn_cin B A) A)
      (.classEq (syn_cdif B (syn_cdif B A)) A) p0000 p0011
  exact p0012

@[expose]
noncomputable def g_dfun2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cun A B) (syn_cdif (syn_cvv) (syn_cdif (syn_cdif (syn_cvv) A) B))) :=
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
  have p0000 := @g_vex x
  have p0001 := @g_eldif (.cv x) (syn_cvv) A
  have p0002 :=
    @g_mpbiran (.classMem (.cv x) (syn_cdif (syn_cvv) A)) (.classMem (.cv x) (syn_cvv))
      (.neg (.classMem (.cv x) A)) p0000 p0001
  have p0003 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdif (syn_cvv) A)) (.neg (.classMem (.cv x) A))
      (.neg (.classMem (.cv x) B)) p0002
  have p0004 := @g_eldif (.cv x) (syn_cdif (syn_cvv) A) B
  have p0005 := @g_ioran (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0006 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (.cv x) (syn_cdif (syn_cvv) A)) (.neg (.classMem (.cv x) B)))
      (syn_wa (.neg (.classMem (.cv x) A)) (.neg (.classMem (.cv x) B)))
      (.classMem (.cv x) (syn_cdif (syn_cdif (syn_cvv) A) B))
      (.neg (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))) p0003 p0004 p0005
  have p0007 :=
    @g_con2bii (.classMem (.cv x) (syn_cdif (syn_cdif (syn_cvv) A) B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) p0006
  have p0008 := @g_eldif (.cv x) (syn_cvv) (syn_cdif (syn_cdif (syn_cvv) A) B)
  have p0009 :=
    @g_mpbiran
      (.classMem (.cv x) (syn_cdif (syn_cvv) (syn_cdif (syn_cdif (syn_cvv) A) B)))
      (.classMem (.cv x) (syn_cvv))
      (.neg (.classMem (.cv x) (syn_cdif (syn_cdif (syn_cvv) A) B))) p0000 p0008
  have p0010 :=
    @g_bitr4i (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.neg (.classMem (.cv x) (syn_cdif (syn_cdif (syn_cvv) A) B)))
      (.classMem (.cv x) (syn_cdif (syn_cvv) (syn_cdif (syn_cdif (syn_cvv) A) B))) p0007
      p0009
  have p0011 :=
    @g_uneqri x A B (syn_cdif (syn_cvv) (syn_cdif (syn_cdif (syn_cvv) A) B))
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

@[expose]
noncomputable def g_dfin2 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin A B) (syn_cdif A (syn_cdif (syn_cvv) B))) :=
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
  have p0000 := @g_vex x
  have p0001 := @g_eldif (.cv x) (syn_cvv) B
  have p0002 :=
    @g_mpbiran (.classMem (.cv x) (syn_cdif (syn_cvv) B)) (.classMem (.cv x) (syn_cvv))
      (.neg (.classMem (.cv x) B)) p0000 p0001
  have p0003 :=
    @g_con2bii (.classMem (.cv x) (syn_cdif (syn_cvv) B)) (.classMem (.cv x) B) p0002
  have p0004 :=
    @g_anbi2i (.classMem (.cv x) B) (.neg (.classMem (.cv x) (syn_cdif (syn_cvv) B)))
      (.classMem (.cv x) A) p0003
  have p0005 := @g_eldif (.cv x) A (syn_cdif (syn_cvv) B)
  have p0006 :=
    @g_bitr4i (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_cdif (syn_cvv) B))))
      (.classMem (.cv x) (syn_cdif A (syn_cdif (syn_cvv) B))) p0004 p0005
  have p0007 :=
    @g_ineqri x A B (syn_cdif A (syn_cdif (syn_cvv) B))
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

@[expose]
noncomputable def g_difin (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cdif A (syn_cin A B)) (syn_cdif A B)) :=
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
  have p0000 := @g_pm4_61 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @g_anclb (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0002 := @g_elin (.cv x) A B
  have p0003 :=
    @g_imbi2i (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) A) p0002
  have p0004 := @g_iman (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin A B))
  have p0005 :=
    @g_n_3bitr2i (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin A B)))
      (.neg (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_cin A B))))) p0001
      p0003 p0004
  have p0006 :=
    @g_con2bii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_cin A B)))) p0005
  have p0007 := @g_eldif (.cv x) A B
  have p0008 :=
    @g_n_3bitr4i (.neg (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_cin A B))))
      (.classMem (.cv x) (syn_cdif A B)) p0000 p0006 p0007
  have p0009 :=
    @g_difeqri x A (syn_cin A B) (syn_cdif A B)
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

@[expose]
noncomputable def g_dfun3 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cun A B)
        (syn_cdif (syn_cvv) (syn_cin (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) B)))) :=
  by
  have p0000 := @g_dfun2 A B
  have p0001 := @g_dfin2 (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) B)
  have p0002 := @g_ddif B
  have p0003 :=
    @g_difeq2i (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) B)) B (syn_cdif (syn_cvv) A) p0002
  have p0004 :=
    @g_eqtr2i (syn_cin (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) B))
      (syn_cdif (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) B)))
      (syn_cdif (syn_cdif (syn_cvv) A) B) p0001 p0003
  have p0005 :=
    @g_difeq2i (syn_cdif (syn_cdif (syn_cvv) A) B)
      (syn_cin (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) B)) (syn_cvv) p0004
  have p0006 :=
    @g_eqtri (syn_cun A B) (syn_cdif (syn_cvv) (syn_cdif (syn_cdif (syn_cvv) A) B))
      (syn_cdif (syn_cvv) (syn_cin (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) B))) p0000
      p0005
  exact p0006

@[expose]
noncomputable def g_dfin4 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin A B) (syn_cdif A (syn_cdif A B))) :=
  by
  have p0000 := @g_inss1 A B
  have p0001 := @g_dfss4 (syn_cin A B) A
  have p0002 :=
    @g_mpbi (syn_wss (syn_cin A B) A)
      (.classEq (syn_cdif A (syn_cdif A (syn_cin A B))) (syn_cin A B)) p0000 p0001
  have p0003 := @g_difin A B
  have p0004 := @g_difeq2i (syn_cdif A (syn_cin A B)) (syn_cdif A B) A p0003
  have p0005 :=
    @g_eqtr3i (syn_cdif A (syn_cdif A (syn_cin A B))) (syn_cin A B)
      (syn_cdif A (syn_cdif A B)) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_invdif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_cdif (syn_cvv) B)) (syn_cdif A B)) :=
  by
  have p0000 := @g_dfin2 A (syn_cdif (syn_cvv) B)
  have p0001 := @g_ddif B
  have p0002 := @g_difeq2i (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) B)) B A p0001
  have p0003 :=
    @g_eqtri (syn_cin A (syn_cdif (syn_cvv) B))
      (syn_cdif A (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) B))) (syn_cdif A B) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_indi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cin A (syn_cun B C)) (syn_cun (syn_cin A B) (syn_cin A C))) :=
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
  have p0000 := @g_andi (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0001 := @g_elin (.cv x) A B
  have p0002 := @g_elin (.cv x) A C
  have p0003 :=
    @g_orbi12i (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classMem (.cv x) (syn_cin A C))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)) p0001 p0002
  have p0004 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
        (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (syn_wo (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) (syn_cin A C))) p0000
      p0003
  have p0005 := @g_elun (.cv x) B C
  have p0006 :=
    @g_anbi2i (.classMem (.cv x) (syn_cun B C))
      (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0005
  have p0007 := @g_elun (.cv x) (syn_cin A B) (syn_cin A C)
  have p0008 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (syn_wo (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) (syn_cin A C)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_cun B C)))
      (.classMem (.cv x) (syn_cun (syn_cin A B) (syn_cin A C))) p0004 p0006 p0007
  have p0009 :=
    @g_ineqri x A (syn_cun B C) (syn_cun (syn_cin A B) (syn_cin A C))
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

@[expose]
noncomputable def g_undi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cun A (syn_cin B C)) (syn_cin (syn_cun A B) (syn_cun A C))) :=
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
  have p0000 := @g_elin (.cv x) B C
  have p0001 :=
    @g_orbi2i (.classMem (.cv x) (syn_cin B C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0000
  have p0002 := @g_ordi (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0003 := @g_elin (.cv x) (syn_cun A B) (syn_cun A C)
  have p0004 := @g_elun (.cv x) A B
  have p0005 := @g_elun (.cv x) A C
  have p0006 :=
    @g_anbi12i (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classMem (.cv x) (syn_cun A C))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) C)) p0004 p0005
  have p0007 :=
    @g_bitr2i (.classMem (.cv x) (syn_cin (syn_cun A B) (syn_cun A C)))
      (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv x) (syn_cun A C)))
      (syn_wa (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
        (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) C)))
      p0003 p0006
  have p0008 :=
    @g_n_3bitri (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) (syn_cin B C)))
      (syn_wo (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (syn_wa (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
        (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (.classMem (.cv x) (syn_cin (syn_cun A B) (syn_cun A C))) p0001 p0002 p0007
  have p0009 :=
    @g_uneqri x A (syn_cin B C) (syn_cin (syn_cun A B) (syn_cun A C))
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

@[expose]
noncomputable def g_indir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cin (syn_cun A B) C) (syn_cun (syn_cin A C) (syn_cin B C))) :=
  by
  have p0000 := @g_indi C A B
  have p0001 := @g_incom (syn_cun A B) C
  have p0002 := @g_incom A C
  have p0003 := @g_incom B C
  have p0004 :=
    @g_uneq12i (syn_cin A C) (syn_cin C A) (syn_cin B C) (syn_cin C B) p0002 p0003
  have p0005 :=
    @g_n_3eqtr4i (syn_cin C (syn_cun A B)) (syn_cun (syn_cin C A) (syn_cin C B))
      (syn_cin (syn_cun A B) C) (syn_cun (syn_cin A C) (syn_cin B C)) p0000 p0001 p0004
  exact p0005

@[expose]
noncomputable def g_undir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cun (syn_cin A B) C) (syn_cin (syn_cun A C) (syn_cun B C))) :=
  by
  have p0000 := @g_undi C A B
  have p0001 := @g_uncom (syn_cin A B) C
  have p0002 := @g_uncom A C
  have p0003 := @g_uncom B C
  have p0004 :=
    @g_ineq12i (syn_cun A C) (syn_cun C A) (syn_cun B C) (syn_cun C B) p0002 p0003
  have p0005 :=
    @g_n_3eqtr4i (syn_cun C (syn_cin A B)) (syn_cin (syn_cun C A) (syn_cun C B))
      (syn_cun (syn_cin A B) C) (syn_cin (syn_cun A C) (syn_cun B C)) p0000 p0001 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay
