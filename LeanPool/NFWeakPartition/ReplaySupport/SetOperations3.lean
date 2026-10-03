/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SetOperations2


/-! NF weak partition development: NominalWPPReplayChunk008. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_unisng (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_cuni (syn_csn A)) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_sneq (.cv x) A
  have p0001 := @g_unieqd (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) p0000
  have p0002 := @g_id (.classEq (.cv x) A)
  have p0003 :=
    @g_eqeq12d (.classEq (.cv x) A) (syn_cuni (syn_csn (.cv x))) (syn_cuni (syn_csn A))
      (.cv x) A p0001 p0002
  have p0004 := @g_vex x
  have p0005 := @g_unisn (.cv x) p0004
  have p0006 :=
    @g_vtoclg (.classEq (syn_cuni (syn_csn (.cv x))) (.cv x))
      (.classEq (syn_cuni (syn_csn A)) A) x A V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0003 p0005
  exact p0006

@[expose]
noncomputable def g_uniun (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cuni (syn_cun A B)) (syn_cun (syn_cuni A) (syn_cuni B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_n_19_43 (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
      (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)) y
  have p0001 := @g_elun (.cv y) A B
  have p0002 :=
    @g_anbi2i (.classMem (.cv y) (syn_cun A B))
      (syn_wo (.classMem (.cv y) A) (.classMem (.cv y) B)) (.classMem (.cv x) (.cv y))
      p0001
  have p0003 :=
    @g_andi (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A) (.classMem (.cv y) B)
  have p0004 :=
    @g_bitri (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cun A B)))
      (syn_wa (.classMem (.cv x) (.cv y)) (syn_wo (.classMem (.cv y) A) (.classMem (.cv y) B)))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
        (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)))
      p0002 p0003
  have p0005 :=
    @g_exbii (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cun A B)))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
        (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)))
      y p0004
  have p0006 :=
    @g_eluni y (.cv x) A
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
  have p0007 :=
    @g_eluni y (.cv x) B
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
  have p0008 :=
    @g_orbi12i (.classMem (.cv x) (syn_cuni A))
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
      (.classMem (.cv x) (syn_cuni B))
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))) p0006 p0007
  have p0009 :=
    @g_n_3bitr4i
      (syn_wex y (syn_wo (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
          (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))))
      (syn_wo (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
        (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))))
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cun A B))))
      (syn_wo (.classMem (.cv x) (syn_cuni A)) (.classMem (.cv x) (syn_cuni B))) p0000
      p0005 p0008
  have p0010 :=
    @g_eluni y (.cv x) (syn_cun A B)
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
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
  have p0011 := @g_elun (.cv x) (syn_cuni A) (syn_cuni B)
  have p0012 :=
    @g_n_3bitr4i
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cun A B))))
      (syn_wo (.classMem (.cv x) (syn_cuni A)) (.classMem (.cv x) (syn_cuni B)))
      (.classMem (.cv x) (syn_cuni (syn_cun A B)))
      (.classMem (.cv x) (syn_cun (syn_cuni A) (syn_cuni B))) p0009 p0010 p0011
  have p0013 :=
    @g_eqriv x (syn_cuni (syn_cun A B)) (syn_cun (syn_cuni A) (syn_cuni B))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              Finset.mem_union] at ⊢;
            aesop))
      p0012
  exact p0013

@[expose]
noncomputable def g_uniss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cuni A) (syn_cuni B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_ssel A B (.cv y)
  have p0001 :=
    @g_anim2d (syn_wss A B) (.classMem (.cv y) A) (.classMem (.cv y) B)
      (.classMem (.cv x) (.cv y)) p0000
  have p0002 :=
    @g_eximdv (syn_wss A B) (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
      (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)) y
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
    @g_eluni y (.cv x) A
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
  have p0004 :=
    @g_eluni y (.cv x) B
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
  have p0005 :=
    @g_n_3imtr4g (syn_wss A B)
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)))
      (.classMem (.cv x) (syn_cuni A)) (.classMem (.cv x) (syn_cuni B)) p0002 p0003 p0004
  have p0006 :=
    @g_ssrdv (syn_wss A B) x (syn_cuni A) (syn_cuni B)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni] at ⊢;
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
      p0005
  exact p0006

@[expose]
noncomputable def g_ssuni (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wss A B) (.classMem B C)) (syn_wss A (syn_cuni C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 := @g_eleq2 (.cv x) B (.cv y)
  have p0001 :=
    @g_imbi1d (.classEq (.cv x) B) (.classMem (.cv y) (.cv x)) (.classMem (.cv y) B)
      (.classMem (.cv y) (syn_cuni C)) p0000
  have p0002 := @g_elunii (.cv y) (.cv x) C
  have p0003 :=
    @g_expcom (.classMem (.cv y) (.cv x)) (.classMem (.cv x) C)
      (.classMem (.cv y) (syn_cuni C)) p0002
  have p0004 :=
    @g_vtoclga (.imp (.classMem (.cv y) (.cv x)) (.classMem (.cv y) (syn_cuni C)))
      (.imp (.classMem (.cv y) B) (.classMem (.cv y) (syn_cuni C))) x B C
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
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0001 p0003
  have p0005 :=
    @g_imim2d (.classMem B C) (.classMem (.cv y) B) (.classMem (.cv y) (syn_cuni C))
      (.classMem (.cv y) A) p0004
  have p0006 :=
    @g_alimdv (.classMem B C) (.imp (.classMem (.cv y) A) (.classMem (.cv y) B))
      (.imp (.classMem (.cv y) A) (.classMem (.cv y) (syn_cuni C))) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      p0005
  have p0007 :=
    @g_dfss2 y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @g_dfss2 y A (syn_cuni C)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni] at ⊢;
            aesop))
  have p0009 :=
    @g_n_3imtr4g (.classMem B C)
      (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv y) B)))
      (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv y) (syn_cuni C)))) (syn_wss A B)
      (syn_wss A (syn_cuni C)) p0006 p0007 p0008
  have p0010 := @g_impcom (.classMem B C) (syn_wss A B) (syn_wss A (syn_cuni C)) p0009
  exact p0010

@[expose]
noncomputable def g_uni0b (A : Class) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cuni A) (syn_c0)) (syn_wss A (syn_csn (syn_c0)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_elsn x (syn_c0)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
  have p0001 :=
    @g_ralbii (.classMem (.cv x) (syn_csn (syn_c0))) (.classEq (.cv x) (syn_c0)) x A p0000
  have p0002 :=
    @g_dfss3 x A (syn_csn (syn_c0))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
  have p0003 :=
    @g_neq0 y (syn_cuni A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni] at ⊢;
            aesop))
  have p0004 :=
    @g_rexcom4 (.classMem (.cv y) (.cv x)) x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_neq0 y (.cv x)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 :=
    @g_rexbii (.neg (.classEq (.cv x) (syn_c0))) (syn_wex y (.classMem (.cv y) (.cv x))) x
      A p0005
  have p0007 :=
    @g_eluni2 x (.cv y) A
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
  have p0008 :=
    @g_exbii (.classMem (.cv y) (syn_cuni A)) (syn_wrex x A (.classMem (.cv y) (.cv x))) y
      p0007
  have p0009 :=
    @g_n_3bitr4ri (syn_wrex x A (syn_wex y (.classMem (.cv y) (.cv x))))
      (syn_wex y (syn_wrex x A (.classMem (.cv y) (.cv x))))
      (syn_wrex x A (.neg (.classEq (.cv x) (syn_c0))))
      (syn_wex y (.classMem (.cv y) (syn_cuni A))) p0004 p0006 p0008
  have p0010 := @g_rexnal (.classEq (.cv x) (syn_c0)) x A
  have p0011 :=
    @g_n_3bitri (.neg (.classEq (syn_cuni A) (syn_c0)))
      (syn_wex y (.classMem (.cv y) (syn_cuni A)))
      (syn_wrex x A (.neg (.classEq (.cv x) (syn_c0))))
      (.neg (syn_wral x A (.classEq (.cv x) (syn_c0)))) p0003 p0009 p0010
  have p0012 :=
    @g_con4bii (.classEq (syn_cuni A) (syn_c0)) (syn_wral x A (.classEq (.cv x) (syn_c0)))
      p0011
  have p0013 :=
    @g_n_3bitr4ri (syn_wral x A (.classMem (.cv x) (syn_csn (syn_c0))))
      (syn_wral x A (.classEq (.cv x) (syn_c0))) (syn_wss A (syn_csn (syn_c0)))
      (.classEq (syn_cuni A) (syn_c0)) p0001 p0002 p0012
  exact p0013

@[expose]
noncomputable def g_uni0 : Nominal.NPrf (.classEq (syn_cuni (syn_c0)) (syn_c0)) :=
  by
  have p0000 := @g_n_0ss (syn_csn (syn_c0))
  have p0001 := @g_uni0b (syn_c0)
  have p0002 :=
    @g_mpbir (.classEq (syn_cuni (syn_c0)) (syn_c0)) (syn_wss (syn_c0) (syn_csn (syn_c0)))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elssuni (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (syn_wss A (syn_cuni B))) :=
  by
  have p0000 := @g_ssid A
  have p0001 := @g_ssuni A A B
  have p0002 := @g_mpan (syn_wss A A) (.classMem A B) (syn_wss A (syn_cuni B)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_dfint2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cint A) (.cab x (syn_wral y A (.classMem (.cv x) (.cv y))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_int x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (syn_wral y A (.classMem (.cv x) (.cv y))))
  have p0002 :=
    @g_abbii (syn_wral y A (.classMem (.cv x) (.cv y)))
      (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))) x p0001
  have p0003_e00_recanon :
    Nominal.NPrf
      (.classEq (syn_cint A)
        (.cab x (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _)
      p0000
  have p0003 :=
    @g_eqtr4i (syn_cint A)
      (.cab x (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))))
      (.cab x (syn_wral y A (.classMem (.cv x) (.cv y)))) p0003_e00_recanon p0002
  exact p0003

@[expose]
noncomputable def g_inteq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cint A) (syn_cint B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_raleq (.classMem (.cv x) (.cv y)) y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wral y A (.classMem (.cv x) (.cv y)))
      (syn_wral y B (.classMem (.cv x) (.cv y))) x
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
    @g_dfint2 x y A
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
    @g_dfint2 x y B
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
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wral y A (.classMem (.cv x) (.cv y))))
      (.cab x (syn_wral y B (.classMem (.cv x) (.cv y)))) (syn_cint A) (syn_cint B) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_inteqi (A : Class) (B : Class)
    (hyp_inteqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cint A) (syn_cint B)) :=
  by
  have p0000 := @g_inteq A B
  have p0001 := Nominal.mp hyp_inteqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_elint (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_elint_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cint B))
        (.all x (.imp (.classMem (.cv x) B) (.classMem A (.cv x))))) :=
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
  have p0000 := @g_eleq1 (.cv y) A (.cv x)
  have p0001 :=
    @g_imbi2d (.classEq (.cv y) A) (.classMem (.cv y) (.cv x)) (.classMem A (.cv x))
      (.classMem (.cv x) B) p0000
  have p0002 :=
    @g_albidv (.classEq (.cv y) A)
      (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x)))
      (.imp (.classMem (.cv x) B) (.classMem A (.cv x))) x
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_int y x B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004_e02_recanon :
    Nominal.NPrf
      (.classEq (syn_cint B)
        (.cab y (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _)
      p0003
  have p0004 :=
    @g_elab2 (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x))))
      (.all x (.imp (.classMem (.cv x) B) (.classMem A (.cv x)))) y A (syn_cint B)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      hyp_elint_1 p0002 p0004_e02_recanon
  exact p0004

@[expose]
noncomputable def g_elint2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_elint2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cint B)) (syn_wral x B (.classMem A (.cv x)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_elint x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_elint2_1
  have p0001 := (Nominal.biimpRefl (syn_wral x B (.classMem A (.cv x))))
  have p0002 :=
    @g_bitr4i (.classMem A (syn_cint B))
      (.all x (.imp (.classMem (.cv x) B) (.classMem A (.cv x))))
      (syn_wral x B (.classMem A (.cv x))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elintab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_inteqab_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cint (.cab x ph))) (.all x (.imp ph (.classMem A (.cv x))))) :=
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
  have p0000 :=
    @g_elint y A (.cab x ph)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      hyp_inteqab_1
  have p0001 :=
    @g_nfsab1 ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfv (.classMem A (.cv y)) x
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
  have p0003 :=
    @g_nfim (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y)) x p0001 p0002
  have p0004 :=
    @g_nfv (.imp ph (.classMem A (.cv x))) y
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @g_eleq1 (.cv y) (.cv x) (.cab x ph)
  have p0006 := @g_abid ph x
  have p0007 :=
    @g_syl6bb (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph))
      (.classMem (.cv x) (.cab x ph)) ph p0005 p0006
  have p0008 := @g_eleq2 (.cv y) (.cv x) A
  have p0009 :=
    @g_imbi12d (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph)) ph
      (.classMem A (.cv y)) (.classMem A (.cv x)) p0007 p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq y x) (syn_wb (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y)))
          (.imp ph (.classMem A (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_cbval (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y)))
      (.imp ph (.classMem A (.cv x))) y x p0003 p0004 p0010_e02_recanon
  have p0011 :=
    @g_bitri (.classMem A (syn_cint (.cab x ph)))
      (.all y (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y))))
      (.all x (.imp ph (.classMem A (.cv x)))) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_intss1 (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (syn_wss (syn_cint B) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_vex x
  have p0001 :=
    @g_elint y (.cv x) B
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
      p0000
  have p0002 := @g_eleq1 (.cv y) A B
  have p0003 := @g_eleq2 (.cv y) A (.cv x)
  have p0004 :=
    @g_imbi12d (.classEq (.cv y) A) (.classMem (.cv y) B) (.classMem A B)
      (.classMem (.cv x) (.cv y)) (.classMem (.cv x) A) p0002 p0003
  have p0005 :=
    @g_spcgv (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y)))
      (.imp (.classMem A B) (.classMem (.cv x) A)) y A B
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0004
  have p0006 :=
    @g_pm2_43a (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y))))
      (.classMem A B) (.classMem (.cv x) A) p0005
  have p0007 :=
    @g_syl5bi (.classMem (.cv x) (syn_cint B))
      (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y)))) (.classMem A B)
      (.classMem (.cv x) A) p0001 p0006
  have p0008 :=
    @g_ssrdv (.classMem A B) x (syn_cint B) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint] at ⊢;
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
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      p0007
  exact p0008

@[expose]
noncomputable def g_ssint (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cint B)) (syn_wral x B (syn_wss A (.cv x)))) :=
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
    @g_dfss3 y A (syn_cint B)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint] at ⊢;
            aesop))
  have p0001 := @g_vex y
  have p0002 :=
    @g_elint2 x (.cv y) B
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
      p0001
  have p0003 :=
    @g_ralbii (.classMem (.cv y) (syn_cint B)) (syn_wral x B (.classMem (.cv y) (.cv x)))
      y A p0002
  have p0004 :=
    @g_ralcom (.classMem (.cv y) (.cv x)) y x A B
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
    @g_dfss3 y A (.cv x)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 :=
    @g_ralbii (syn_wss A (.cv x)) (syn_wral y A (.classMem (.cv y) (.cv x))) x B p0005
  have p0007 :=
    @g_bitr4i (syn_wral y A (syn_wral x B (.classMem (.cv y) (.cv x))))
      (syn_wral x B (syn_wral y A (.classMem (.cv y) (.cv x))))
      (syn_wral x B (syn_wss A (.cv x))) p0004 p0006
  have p0008 :=
    @g_n_3bitri (syn_wss A (syn_cint B)) (syn_wral y A (.classMem (.cv y) (syn_cint B)))
      (syn_wral y A (syn_wral x B (.classMem (.cv y) (.cv x))))
      (syn_wral x B (syn_wss A (.cv x))) p0000 p0003 p0007
  exact p0008

@[expose]
noncomputable def g_ssintab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (syn_wss A (syn_cint (.cab x ph))) (.all x (.imp ph (syn_wss A (.cv x))))) :=
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
  have p0000 :=
    @g_ssint y A (.cab x ph)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0001 := @g_sseq2 (.cv y) (.cv x) A
  have p0002_e00_recanon :
    Nominal.NPrf (.imp (.objEq y x) (syn_wb (syn_wss A (.cv y)) (syn_wss A (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @g_ralab2 ph (syn_wss A (.cv y)) (syn_wss A (.cv x)) y x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
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
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0002_e00_recanon
  have p0003 :=
    @g_bitri (syn_wss A (syn_cint (.cab x ph)))
      (syn_wral y (.cab x ph) (syn_wss A (.cv y))) (.all x (.imp ph (syn_wss A (.cv x))))
      p0000 p0002
  exact p0003

@[expose]
noncomputable def g_ssmin (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wss A (syn_cint (.cab x (syn_wa (syn_wss A (.cv x)) ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_ssintab (syn_wa (syn_wss A (.cv x)) ph) x A
      (by
        first
        | (aesop))
  have p0001 := @g_simpl (syn_wss A (.cv x)) ph
  have p0002 :=
    @g_mpgbir (syn_wss A (syn_cint (.cab x (syn_wa (syn_wss A (.cv x)) ph))))
      (.imp (syn_wa (syn_wss A (.cv x)) ph) (syn_wss A (.cv x))) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eliun (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_ciun x B C)) (syn_wrex x B (.classMem A C))) :=
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
  have p0000 := @g_elex A (syn_ciun x B C)
  have p0001 := @g_elex A C
  have p0002 :=
    @g_rexlimivw (.classMem A C) (.classMem A (syn_cvv)) x B
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
      p0001
  have p0003 := @g_eleq1 (.cv y) A C
  have p0004 :=
    @g_rexbidv (.classEq (.cv y) A) (.classMem (.cv y) C) (.classMem A C) x B
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x y B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    @g_elab2g (syn_wrex x B (.classMem (.cv y) C)) (syn_wrex x B (.classMem A C)) y A
      (syn_ciun x B C) (syn_cvv)
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
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0004 p0005
  have p0007 :=
    @g_pm5_21nii (.classMem A (syn_ciun x B C)) (.classMem A (syn_cvv))
      (syn_wrex x B (.classMem A C)) p0000 p0002 p0006
  exact p0007

@[expose]
noncomputable def g_ss2iun (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wral x A (syn_wss B C)) (syn_wss (syn_ciun x A B) (syn_ciun x A C))) :=
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
  have p0000 := @g_ssel B C (.cv y)
  have p0001 :=
    @g_ralimi (syn_wss B C) (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)) x A p0000
  have p0002 := @g_rexim (.classMem (.cv y) B) (.classMem (.cv y) C) x A
  have p0003 :=
    @g_syl (syn_wral x A (syn_wss B C))
      (syn_wral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)))
      (.imp (syn_wrex x A (.classMem (.cv y) B)) (syn_wrex x A (.classMem (.cv y) C)))
      p0001 p0002
  have p0004 :=
    @g_eliun x (.cv y) A B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @g_eliun x (.cv y) A C
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 :=
    @g_n_3imtr4g (syn_wral x A (syn_wss B C)) (syn_wrex x A (.classMem (.cv y) B))
      (syn_wrex x A (.classMem (.cv y) C)) (.classMem (.cv y) (syn_ciun x A B))
      (.classMem (.cv y) (syn_ciun x A C)) p0003 p0004 p0005
  have p0007 :=
    @g_ssrdv (syn_wral x A (syn_wss B C)) y (syn_ciun x A B) (syn_ciun x A C)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0006
  exact p0007

@[expose]
noncomputable def g_iuneq2 (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wral x A (.classEq B C)) (.classEq (syn_ciun x A B) (syn_ciun x A C))) :=
  by
  have p0000 := @g_ss2iun x A B C
  have p0001 := @g_ss2iun x A C B
  have p0002 :=
    @g_anim12i (syn_wral x A (syn_wss B C)) (syn_wss (syn_ciun x A B) (syn_ciun x A C))
      (syn_wral x A (syn_wss C B)) (syn_wss (syn_ciun x A C) (syn_ciun x A B)) p0000 p0001
  have p0003 := @g_eqss B C
  have p0004 := @g_ralbii (.classEq B C) (syn_wa (syn_wss B C) (syn_wss C B)) x A p0003
  have p0005 := @g_r19_26 (syn_wss B C) (syn_wss C B) x A
  have p0006 :=
    @g_bitri (syn_wral x A (.classEq B C))
      (syn_wral x A (syn_wa (syn_wss B C) (syn_wss C B)))
      (syn_wa (syn_wral x A (syn_wss B C)) (syn_wral x A (syn_wss C B))) p0004 p0005
  have p0007 := @g_eqss (syn_ciun x A B) (syn_ciun x A C)
  have p0008 :=
    @g_n_3imtr4i (syn_wa (syn_wral x A (syn_wss B C)) (syn_wral x A (syn_wss C B)))
      (syn_wa (syn_wss (syn_ciun x A B) (syn_ciun x A C))
        (syn_wss (syn_ciun x A C) (syn_ciun x A B)))
      (syn_wral x A (.classEq B C)) (.classEq (syn_ciun x A B) (syn_ciun x A C)) p0002
      p0006 p0007
  exact p0008

@[expose]
noncomputable def g_iuneq2i (x : Var) (A : Class) (B : Class) (C : Class)
    (hyp_iuneq2i_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.classEq B C))) :
    Nominal.NPrf (.classEq (syn_ciun x A B) (syn_ciun x A C)) :=
  by
  have p0000 := @g_iuneq2 x A B C
  have p0001 :=
    @g_mprg (.classEq B C) (.classEq (syn_ciun x A B) (syn_ciun x A C)) x A p0000
      hyp_iuneq2i_1
  exact p0001

@[expose]
noncomputable def g_nfiun (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_nfiun_1 : Nominal.NPrf (syn_wnfc y A))
    (hyp_nfiun_2 : Nominal.NPrf (syn_wnfc y B)) :
    Nominal.NPrf (syn_wnfc y (syn_ciun x A B)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x z A B
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
    @g_nfcri y z B
      (by
        first
        | (aesop))
      hyp_nfiun_2
  have p0002 := @g_nfrex (.classMem (.cv z) B) y x A hyp_nfiun_1 p0001
  have p0003 := @g_nfab (syn_wrex x A (.classMem (.cv z) B)) y z p0002
  have p0004 :=
    @g_nfcxfr y (syn_ciun x A B) (.cab z (syn_wrex x A (.classMem (.cv z) B))) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfiu1 (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf (syn_wnfc x (syn_ciun x A B)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_nfre1 (.classMem (.cv y) B) x A
  have p0002 := @g_nfab (syn_wrex x A (.classMem (.cv y) B)) x y p0001
  have p0003 :=
    @g_nfcxfr x (syn_ciun x A B) (.cab y (syn_wrex x A (.classMem (.cv y) B))) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_dfiun2g (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wral x A (.classMem B C)) (.classEq (syn_ciun x A B)
          (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
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
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 := @g_nfra1 (.classMem B C) x A
  have p0001 := @g_rsp (.classMem B C) x A
  have p0002 :=
    @g_clel3g y (.cv z) B C
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
  have p0003 :=
    @g_syl6 (syn_wral x A (.classMem B C)) (.classMem (.cv x) A) (.classMem B C)
      (syn_wb (.classMem (.cv z) B)
        (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      p0001 p0002
  have p0004 :=
    @g_imp (syn_wral x A (.classMem B C)) (.classMem (.cv x) A)
      (syn_wb (.classMem (.cv z) B)
        (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      p0003
  have p0005 :=
    @g_rexbida (syn_wral x A (.classMem B C)) (.classMem (.cv z) B)
      (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))) x A p0000
      p0004
  have p0006 :=
    @g_rexcom4 (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))) x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0007 :=
    @g_syl6bb (syn_wral x A (.classMem B C)) (syn_wrex x A (.classMem (.cv z) B))
      (syn_wrex x A (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      (syn_wex y (syn_wrex x A (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      p0005 p0006
  have p0008 :=
    @g_r19_41v (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)) x A
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
  have p0009 :=
    @g_exbii (syn_wrex x A (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))))
      (syn_wa (syn_wrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y))) y p0008
  have p0010 :=
    @g_exancom (syn_wrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y)) y
  have p0011 :=
    @g_bitri
      (syn_wex y (syn_wrex x A (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      (syn_wex y (syn_wa (syn_wrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv z) (.cv y)) (syn_wrex x A (.classEq (.cv y) B))))
      p0009 p0010
  have p0012 :=
    @g_syl6bb (syn_wral x A (.classMem B C)) (syn_wrex x A (.classMem (.cv z) B))
      (syn_wex y (syn_wrex x A (syn_wa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      (syn_wex y (syn_wa (.classMem (.cv z) (.cv y)) (syn_wrex x A (.classEq (.cv y) B))))
      p0007 p0011
  have p0013 :=
    @g_eliun x (.cv z) A B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0014 :=
    @g_eluniab (syn_wrex x A (.classEq (.cv y) B)) y (.cv z)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0015 :=
    @g_n_3bitr4g (syn_wral x A (.classMem B C)) (syn_wrex x A (.classMem (.cv z) B))
      (syn_wex y (syn_wa (.classMem (.cv z) (.cv y)) (syn_wrex x A (.classEq (.cv y) B))))
      (.classMem (.cv z) (syn_ciun x A B))
      (.classMem (.cv z) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B))))) p0012
      p0013 p0014
  have p0016 :=
    @g_eqrdv (syn_wral x A (.classMem B C)) z (syn_ciun x A B)
      (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B))))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
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
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0015
  exact p0016

@[expose]
noncomputable def g_dfiun2 (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_dfiun2_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_ciun x A B) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dfiun2g x y A B (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_a1i (.classMem B (syn_cvv)) (.classMem (.cv x) A) hyp_dfiun2_1
  have p0002 :=
    @g_mprg (.classMem B (syn_cvv))
      (.classEq (syn_ciun x A B) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) B)))))
      x A p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cbviun (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbviun_1 : Nominal.NPrf (syn_wnfc y B))
    (hyp_cbviun_2 : Nominal.NPrf (syn_wnfc x C))
    (hyp_cbviun_3 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (syn_ciun x A B) (syn_ciun y A C)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
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
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_nfcri y z B
      (by
        first
        | (aesop))
      hyp_cbviun_1
  have p0001 :=
    @g_nfcri x z C
      (by
        first
        | (aesop))
      hyp_cbviun_2
  have p0002_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.classEq B C)) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_cbviun_3
  have p0002 := @g_eleq2d (.classEq (.cv x) (.cv y)) B C (.cv z) p0002_e00_recanon
  have p0003_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (.classMem (.cv z) B) (.classMem (.cv z) C))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @g_cbvrex (.classMem (.cv z) B) (.classMem (.cv z) C) x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001 p0003_e02_recanon
  have p0004 :=
    @g_abbii (syn_wrex x A (.classMem (.cv z) B)) (syn_wrex y A (.classMem (.cv z) C)) z
      p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x z A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun y z A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0007 :=
    @g_n_3eqtr4i (.cab z (syn_wrex x A (.classMem (.cv z) B)))
      (.cab z (syn_wrex y A (.classMem (.cv z) C))) (syn_ciun x A B) (syn_ciun y A C)
      p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_iunss (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (syn_wb (syn_wss (syn_ciun x A B) C) (syn_wral x A (syn_wss B C))) :=
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
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x y A B
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
    @g_sseq1i (syn_ciun x A B) (.cab y (syn_wrex x A (.classMem (.cv y) B))) C p0000
  have p0002 :=
    @g_abss (syn_wrex x A (.classMem (.cv y) B)) y C
      (by
        first
        | (aesop))
  have p0003 :=
    @g_dfss2 y B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_ralbii (syn_wss B C) (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))) x
      A p0003
  have p0005 :=
    @g_ralcom4 (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)) x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    @g_r19_23v (.classMem (.cv y) B) (.classMem (.cv y) C) x A
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
  have p0007 :=
    @g_albii (syn_wral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)))
      (.imp (syn_wrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C)) y p0006
  have p0008 :=
    @g_n_3bitrri (syn_wral x A (syn_wss B C))
      (syn_wral x A (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))))
      (.all y (syn_wral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))))
      (.all y (.imp (syn_wrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C))) p0004
      p0005 p0007
  have p0009 :=
    @g_n_3bitri (syn_wss (syn_ciun x A B) C)
      (syn_wss (.cab y (syn_wrex x A (.classMem (.cv y) B))) C)
      (.all y (.imp (syn_wrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C)))
      (syn_wral x A (syn_wss B C)) p0001 p0002 p0008
  exact p0009

@[expose]
noncomputable def g_iunab (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_ciun x A (.cab y ph)) (.cab y (syn_wrex x A ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv y A
      (by
        first
        | (aesop))
  have p0001 := @g_nfab1 ph y
  have p0002 := @g_nfiun x y A (.cab y ph) p0000 p0001
  have p0003 := @g_nfab1 (syn_wrex x A ph) y
  have p0004 :=
    @g_cleqf y (syn_ciun x A (.cab y ph)) (.cab y (syn_wrex x A ph)) p0002 p0003
  have p0005 := @g_abid ph y
  have p0006 := @g_rexbii (.classMem (.cv y) (.cab y ph)) ph x A p0005
  have p0007 :=
    @g_eliun x (.cv y) A (.cab y ph)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0008 := @g_abid (syn_wrex x A ph) y
  have p0009 :=
    @g_n_3bitr4i (syn_wrex x A (.classMem (.cv y) (.cab y ph))) (syn_wrex x A ph)
      (.classMem (.cv y) (syn_ciun x A (.cab y ph)))
      (.classMem (.cv y) (.cab y (syn_wrex x A ph))) p0006 p0007 p0008
  have p0010 :=
    @g_mpgbir (.classEq (syn_ciun x A (.cab y ph)) (.cab y (syn_wrex x A ph)))
      (syn_wb (.classMem (.cv y) (syn_ciun x A (.cab y ph)))
        (.classMem (.cv y) (.cab y (syn_wrex x A ph))))
      y p0004 p0009
  exact p0010

@[expose]
noncomputable def g_iunid (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_ciun x A (syn_csn (.cv x))) A) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn y (.cv x)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 := @g_equcom y x
  have p0002_e00_recanon :
    Nominal.NPrf (syn_wb (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0001
  have p0002 :=
    @g_abbii (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y)) y p0002_e00_recanon
  have p0003 :=
    @g_eqtri (syn_csn (.cv x)) (.cab y (.classEq (.cv y) (.cv x)))
      (.cab y (.classEq (.cv x) (.cv y))) p0000 p0002
  have p0004 :=
    @g_a1i (.classEq (syn_csn (.cv x)) (.cab y (.classEq (.cv x) (.cv y))))
      (.classMem (.cv x) A) p0003
  have p0005 := @g_iuneq2i x A (syn_csn (.cv x)) (.cab y (.classEq (.cv x) (.cv y))) p0004
  have p0006 :=
    @g_iunab (.classEq (.cv x) (.cv y)) x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0007 :=
    @g_risset x (.cv y) A
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
  have p0008 :=
    @g_abbii (.classMem (.cv y) A) (syn_wrex x A (.classEq (.cv x) (.cv y))) y p0007
  have p0009 :=
    @g_abid2 y A
      (by
        first
        | (aesop))
  have p0010 :=
    @g_n_3eqtr2i (syn_ciun x A (.cab y (.classEq (.cv x) (.cv y))))
      (.cab y (syn_wrex x A (.classEq (.cv x) (.cv y)))) (.cab y (.classMem (.cv y) A)) A
      p0006 p0008 p0009
  have p0011 :=
    @g_eqtri (syn_ciun x A (syn_csn (.cv x)))
      (syn_ciun x A (.cab y (.classEq (.cv x) (.cv y)))) A p0005 p0010
  exact p0011

@[expose]
noncomputable def g_opkeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_copk A C) (syn_copk B C))) :=
  by
  have p0000 := @g_sneq A B
  have p0001 := @g_preq1 A B C
  have p0002 :=
    @g_preq12d (.classEq A B) (syn_csn A) (syn_csn B) (syn_cpr A C) (syn_cpr B C) p0000
      p0001
  have p0003 := (Nominal.classEqRefl (syn_copk A C))
  have p0004 := (Nominal.classEqRefl (syn_copk B C))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cpr (syn_csn A) (syn_cpr A C))
      (syn_cpr (syn_csn B) (syn_cpr B C)) (syn_copk A C) (syn_copk B C) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_opkeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_copk C A) (syn_copk C B))) :=
  by
  have p0000 := @g_preq2 A B C
  have p0001 := @g_preq2d (.classEq A B) (syn_cpr C A) (syn_cpr C B) (syn_csn C) p0000
  have p0002 := (Nominal.classEqRefl (syn_copk C A))
  have p0003 := (Nominal.classEqRefl (syn_copk C B))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cpr (syn_csn C) (syn_cpr C A))
      (syn_cpr (syn_csn C) (syn_cpr C B)) (syn_copk C A) (syn_copk C B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_opkeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A C) (.classEq B D)) (.classEq (syn_copk A B) (syn_copk C D))) :=
  by
  have p0000 := @g_opkeq1 A C B
  have p0001 := @g_opkeq2 B D C
  have p0002 :=
    @g_sylan9eq (.classEq A C) (.classEq B D) (syn_copk A B) (syn_copk C B) (syn_copk C D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_opkeq2i (A : Class) (B : Class) (C : Class)
    (hyp_opkeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_copk C A) (syn_copk C B)) :=
  by
  have p0000 := @g_opkeq2 A B C
  have p0001 := Nominal.mp hyp_opkeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_opkeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copk A C) (syn_copk B C))) :=
  by
  have p0000 := @g_opkeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_copk A C) (syn_copk B C)) hyp_opkeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_opkeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copk C A) (syn_copk C B))) :=
  by
  have p0000 := @g_opkeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_copk C A) (syn_copk C B)) hyp_opkeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_opkeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_opkeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copk A C) (syn_copk B D))) :=
  by
  have p0000 := @g_opkeq12 A C B D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_copk A C) (syn_copk B D))
      hyp_opkeq1d_1 hyp_opkeq12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_compldif (A : Class) :
    Nominal.NPrf (.classEq (syn_ccompl A) (syn_cdif (syn_cvv) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cdif (syn_cvv) A))
  have p0001 := @g_incom (syn_cvv) (syn_ccompl A)
  have p0002 := @g_inv1 (syn_ccompl A)
  have p0003 :=
    @g_n_3eqtrri (syn_cdif (syn_cvv) A) (syn_cin (syn_cvv) (syn_ccompl A))
      (syn_cin (syn_ccompl A) (syn_cvv)) (syn_ccompl A) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_complV : Nominal.NPrf (.classEq (syn_ccompl (syn_cvv)) (syn_c0)) :=
  by
  have p0000 := @g_compldif (syn_cvv)
  have p0001 := (Nominal.classEqRefl (syn_c0))
  have p0002 :=
    @g_eqtr4i (syn_ccompl (syn_cvv)) (syn_cdif (syn_cvv) (syn_cvv)) (syn_c0) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nincompl (A : Class) :
    Nominal.NPrf (.classEq (syn_cnin A (syn_ccompl A)) (syn_cvv)) :=
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
  have p0000 :=
    @g_eqv x (syn_cnin A (syn_ccompl A))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
              Finset.mem_union] at ⊢;
            aesop))
  have p0001 := @g_pm3_24 (.classMem (.cv x) A)
  have p0002 := @g_vex x
  have p0003 := @g_elnin (.cv x) A (syn_ccompl A) p0002
  have p0004 := @g_elcompl (.cv x) A p0002
  have p0005 :=
    @g_nanbi2i (.classMem (.cv x) (syn_ccompl A)) (.neg (.classMem (.cv x) A))
      (.classMem (.cv x) A) p0004
  have p0006 :=
    (Nominal.biimpRefl (syn_wnan (.classMem (.cv x) A) (.neg (.classMem (.cv x) A))))
  have p0007 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cnin A (syn_ccompl A)))
      (syn_wnan (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))
      (syn_wnan (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))
      (.neg (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))) p0003 p0005 p0006
  have p0008 :=
    @g_mpbir (.classMem (.cv x) (syn_cnin A (syn_ccompl A)))
      (.neg (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))) p0001 p0007
  have p0009 :=
    @g_mpgbir (.classEq (syn_cnin A (syn_ccompl A)) (syn_cvv))
      (.classMem (.cv x) (syn_cnin A (syn_ccompl A))) x p0000 p0008
  exact p0009

@[expose]
noncomputable def g_incompl (A : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_ccompl A)) (syn_c0)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cin A (syn_ccompl A)))
  have p0001 := @g_nincompl A
  have p0002 := @g_compleqi (syn_cnin A (syn_ccompl A)) (syn_cvv) p0001
  have p0003 := @g_complV
  have p0004 :=
    @g_n_3eqtri (syn_cin A (syn_ccompl A)) (syn_ccompl (syn_cnin A (syn_ccompl A)))
      (syn_ccompl (syn_cvv)) (syn_c0) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_uncompl (A : Class) :
    Nominal.NPrf (.classEq (syn_cun A (syn_ccompl A)) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cun A (syn_ccompl A)))
  have p0001 := @g_nincompl (syn_ccompl A)
  have p0002 :=
    @g_eqtri (syn_cun A (syn_ccompl A))
      (syn_cnin (syn_ccompl A) (syn_ccompl (syn_ccompl A))) (syn_cvv) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_inindif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin (syn_cin A B) (syn_cdif A B)) (syn_c0)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cdif A B))
  have p0001 := @g_ineq2i (syn_cdif A B) (syn_cin A (syn_ccompl B)) (syn_cin A B) p0000
  have p0002 := @g_inindi A B (syn_ccompl B)
  have p0003 := @g_incompl B
  have p0004 := @g_ineq2i (syn_cin B (syn_ccompl B)) (syn_c0) A p0003
  have p0005 := @g_in0 A
  have p0006 :=
    @g_eqtri (syn_cin A (syn_cin B (syn_ccompl B))) (syn_cin A (syn_c0)) (syn_c0) p0004
      p0005
  have p0007 :=
    @g_n_3eqtr2i (syn_cin (syn_cin A B) (syn_cdif A B))
      (syn_cin (syn_cin A B) (syn_cin A (syn_ccompl B)))
      (syn_cin A (syn_cin B (syn_ccompl B))) (syn_c0) p0001 p0002 p0006
  exact p0007

@[expose]
noncomputable def g_ssofss (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (.imp (syn_wss A C) (syn_wb (syn_wss A B)
          (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 := @g_vex x
  have p0001 := @g_elcompl (.cv x) C p0000
  have p0002 := @g_ssel A C (.cv x)
  have p0003 := @g_con3d (syn_wss A C) (.classMem (.cv x) A) (.classMem (.cv x) C) p0002
  have p0004 :=
    @g_syl5bi (.classMem (.cv x) (syn_ccompl C)) (.neg (.classMem (.cv x) C))
      (syn_wss A C) (.neg (.classMem (.cv x) A)) p0001 p0003
  have p0005 :=
    @g_imp (syn_wss A C) (.classMem (.cv x) (syn_ccompl C)) (.neg (.classMem (.cv x) A))
      p0004
  have p0006 :=
    @g_pm2_21d (syn_wa (syn_wss A C) (.classMem (.cv x) (syn_ccompl C)))
      (.classMem (.cv x) A) (.classMem (.cv x) B) p0005
  have p0007 :=
    @g_ralrimiva (syn_wss A C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      (syn_ccompl C)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0006
  have p0008 :=
    @g_biantrud (syn_wss A C)
      (syn_wral x (syn_ccompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) p0007
  have p0009 := @g_ralv (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
  have p0010 := @g_uncompl C
  have p0011 :=
    @g_raleqi (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      (syn_cun C (syn_ccompl C)) (syn_cvv)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      p0010
  have p0012 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0013 :=
    @g_n_3bitr4ri
      (syn_wral x (syn_cvv) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wral x (syn_cun C (syn_ccompl C)) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wss A B) p0009 p0011 p0012
  have p0014 :=
    @g_ralunb (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x C (syn_ccompl C)
  have p0015 :=
    @g_bitri (syn_wss A B)
      (syn_wral x (syn_cun C (syn_ccompl C)) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wa (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (syn_wral x (syn_ccompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))))
      p0013 p0014
  have p0016 :=
    @g_syl6rbbr (syn_wss A C)
      (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (syn_wa (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (syn_wral x (syn_ccompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))))
      (syn_wss A B) p0008 p0015
  exact p0016

@[expose]
noncomputable def g_ssofeq (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wss A C) (syn_wss B C)) (syn_wb (.classEq A B)
          (syn_wral x C (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ssofss x A B C
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
    @g_ssofss x B A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_bi2anan9 (syn_wss A C) (syn_wss A B)
      (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (syn_wss B C)
      (syn_wss B A) (syn_wral x C (.imp (.classMem (.cv x) B) (.classMem (.cv x) A)))
      p0000 p0001
  have p0003 := @g_eqss A B
  have p0004 := @g_ralbiim (.classMem (.cv x) A) (.classMem (.cv x) B) x C
  have p0005 :=
    @g_n_3bitr4g (syn_wa (syn_wss A C) (syn_wss B C)) (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (syn_wral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (syn_wral x C (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))))
      (.classEq A B) (syn_wral x C (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_axprimlem1 (B : Class) (a : Var) (c : Var) (dv_B_c : c ∉ B.fv)
    (dv_a_c : a ≠ c) :
    Nominal.NPrf
      (syn_wb (.classEq (.cv a) (syn_csn B))
        (.all c (syn_wb (.objMem c a) (.classEq (.cv c) B)))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ ({ a } : Finset Var) ∪ ({ c } : Finset Var)
  have p0000 :=
    @g_dfcleq c (.cv a) (syn_csn B)
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
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
  have p0001 :=
    @g_elsn c B
      (by
        first
        | (aesop))
  have p0002 :=
    @g_bibi2i (.classMem (.cv c) (syn_csn B)) (.classEq (.cv c) B) (.objMem c a) p0001
  have p0003 :=
    @g_albii (syn_wb (.objMem c a) (.classMem (.cv c) (syn_csn B)))
      (syn_wb (.objMem c a) (.classEq (.cv c) B)) c p0002
  have p0004_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv a) (syn_csn B))
        (.all c (syn_wb (.objMem c a) (.classMem (.cv c) (syn_csn B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0004 :=
    @g_bitri (.classEq (.cv a) (syn_csn B))
      (.all c (syn_wb (.objMem c a) (.classMem (.cv c) (syn_csn B))))
      (.all c (syn_wb (.objMem c a) (.classEq (.cv c) B))) p0004_e00_recanon p0003
  exact p0004

@[expose]
noncomputable def g_ninexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cnin A B) (syn_cvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
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
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_W : w ∉ W.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_w_ne_z : w ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have p0000 := @g_nineq1 (.cv x) A (.cv y)
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cnin (.cv x) (.cv y)) (syn_cnin A (.cv y))
      (syn_cvv) p0000
  have p0002 := @g_nineq2 (.cv y) B A
  have p0003 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_cnin A (.cv y)) (syn_cnin A B) (syn_cvv) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axNin x y z w
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
  have p0005 :=
    @g_isset z (syn_cnin (.cv x) (.cv y))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 :=
    @g_dfcleq w (.cv z) (syn_cnin (.cv x) (.cv y))
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
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0007 := @g_vex w
  have p0008 := @g_elnin (.cv w) (.cv x) (.cv y) p0007
  have p0009_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv w) (syn_cnin (.cv x) (.cv y)))
        (syn_wnan (.objMem w x) (.objMem w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @g_bibi2i (.classMem (.cv w) (syn_cnin (.cv x) (.cv y)))
      (syn_wnan (.objMem w x) (.objMem w y)) (.objMem w z) p0009_e00_recanon
  have p0010 :=
    @g_albii (syn_wb (.objMem w z) (.classMem (.cv w) (syn_cnin (.cv x) (.cv y))))
      (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y))) w p0009
  have p0011_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv z) (syn_cnin (.cv x) (.cv y)))
        (.all w (syn_wb (.objMem w z) (.classMem (.cv w) (syn_cnin (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0011 :=
    @g_bitri (.classEq (.cv z) (syn_cnin (.cv x) (.cv y)))
      (.all w (syn_wb (.objMem w z) (.classMem (.cv w) (syn_cnin (.cv x) (.cv y)))))
      (.all w (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y))))
      p0011_e00_recanon p0010
  have p0012 :=
    @g_exbii (.classEq (.cv z) (syn_cnin (.cv x) (.cv y)))
      (.all w (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y)))) z p0011
  have p0013 :=
    @g_bitri (.classMem (syn_cnin (.cv x) (.cv y)) (syn_cvv))
      (syn_wex z (.classEq (.cv z) (syn_cnin (.cv x) (.cv y))))
      (syn_wex z (.all w (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y)))))
      p0005 p0012
  have p0014 :=
    @g_mpbir (.classMem (syn_cnin (.cv x) (.cv y)) (syn_cvv))
      (syn_wex z (.all w (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y)))))
      p0004 p0013
  have p0015 :=
    @g_vtocl2g (.classMem (syn_cnin (.cv x) (.cv y)) (syn_cvv))
      (.classMem (syn_cnin A (.cv y)) (syn_cvv)) (.classMem (syn_cnin A B) (syn_cvv)) x y
      A B V W
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
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0001 p0003 p0014
  exact p0015

@[expose]
noncomputable def g_complexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_ccompl A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_ccompl A))
  have p0001 := @g_ninexg A A V V
  have p0002 := @g_anidms (.classMem A V) (.classMem (syn_cnin A A) (syn_cvv)) p0001
  have p0003 :=
    @g_syl5eqel (.classMem A V) (syn_ccompl A) (syn_cnin A A) (syn_cvv) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_inexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cin A B) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cin A B))
  have p0001 := @g_ninexg A B V W
  have p0002 := @g_complexg (syn_cnin A B) (syn_cvv)
  have p0003 :=
    @g_syl (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cnin A B) (syn_cvv))
      (.classMem (syn_ccompl (syn_cnin A B)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cin A B)
      (syn_ccompl (syn_cnin A B)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_unexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cun A B) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cun A B))
  have p0001 := @g_complexg A V
  have p0002 := @g_complexg B W
  have p0003 := @g_ninexg (syn_ccompl A) (syn_ccompl B) (syn_cvv) (syn_cvv)
  have p0004 :=
    @g_syl2an (.classMem A V) (.classMem (syn_ccompl A) (syn_cvv))
      (.classMem (syn_ccompl B) (syn_cvv))
      (.classMem (syn_cnin (syn_ccompl A) (syn_ccompl B)) (syn_cvv)) (.classMem B W) p0001
      p0002 p0003
  have p0005 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cun A B)
      (syn_cnin (syn_ccompl A) (syn_ccompl B)) (syn_cvv) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_difexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cdif A B) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cdif A B))
  have p0001 := @g_complexg B W
  have p0002 := @g_inexg A (syn_ccompl B) V (syn_cvv)
  have p0003 :=
    @g_sylan2 (.classMem B W) (.classMem A V) (.classMem (syn_ccompl B) (syn_cvv))
      (.classMem (syn_cin A (syn_ccompl B)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cdif A B)
      (syn_cin A (syn_ccompl B)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_symdifexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_csymdif A B) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_csymdif A B))
  have p0001 := @g_difexg A B V W
  have p0002 := @g_difexg B A W V
  have p0003 :=
    @g_ancoms (.classMem B W) (.classMem A V) (.classMem (syn_cdif B A) (syn_cvv)) p0002
  have p0004 := @g_unexg (syn_cdif A B) (syn_cdif B A) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl2anc (syn_wa (.classMem A V) (.classMem B W))
      (.classMem (syn_cdif A B) (syn_cvv)) (.classMem (syn_cdif B A) (syn_cvv))
      (.classMem (syn_cun (syn_cdif A B) (syn_cdif B A)) (syn_cvv)) p0001 p0003 p0004
  have p0006 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_csymdif A B)
      (syn_cun (syn_cdif A B) (syn_cdif B A)) (syn_cvv) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_complex (A : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ccompl A) (syn_cvv)) :=
  by
  have p0000 := @g_complexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_boolex_1 p0000
  exact p0001

@[expose]
noncomputable def g_inex (A : Class) (B : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_boolex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cin A B) (syn_cvv)) :=
  by
  have p0000 := @g_inexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cin A B) (syn_cvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

@[expose]
noncomputable def g_unex (A : Class) (B : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_boolex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cun A B) (syn_cvv)) :=
  by
  have p0000 := @g_unexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cun A B) (syn_cvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

@[expose]
noncomputable def g_difex (A : Class) (B : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_boolex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cdif A B) (syn_cvv)) :=
  by
  have p0000 := @g_difexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cdif A B) (syn_cvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

@[expose]
noncomputable def g_symdifex (A : Class) (B : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_boolex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_csymdif A B) (syn_cvv)) :=
  by
  have p0000 := @g_symdifexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_csymdif A B) (syn_cvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

@[expose]
noncomputable def g_vvex : Nominal.NPrf (.classMem (syn_cvv) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @g_uncompl (.cv x)
  have p0001 := @g_vex x
  have p0002 := @g_complex (.cv x) p0001
  have p0003 := @g_unex (.cv x) (syn_ccompl (.cv x)) p0001 p0002
  have p0004 :=
    @g_eqeltrri (syn_cun (.cv x) (syn_ccompl (.cv x))) (syn_cvv) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_n_0ex : Nominal.NPrf (.classMem (syn_c0) (syn_cvv)) :=
  by
  have p0000 := @g_complV
  have p0001 := @g_vvex
  have p0002 := @g_complex (syn_cvv) p0001
  have p0003 := @g_eqeltrri (syn_ccompl (syn_cvv)) (syn_c0) (syn_cvv) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_snex (A : Class) : Nominal.NPrf (.classMem (syn_csn A) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 := @g_sneq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axSn x y z
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
    @g_isset y (syn_csn (.cv x))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton] at ⊢;
            aesop))
  have p0004 :=
    @g_axprimlem1 (.cv x) y z
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
  have p0005_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv y) (syn_csn (.cv x)))
        (.all z (syn_wb (.objMem z y) (.objEq z x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_exbii (.classEq (.cv y) (syn_csn (.cv x)))
      (.all z (syn_wb (.objMem z y) (.objEq z x))) y p0005_e00_recanon
  have p0006 :=
    @g_bitri (.classMem (syn_csn (.cv x)) (syn_cvv))
      (syn_wex y (.classEq (.cv y) (syn_csn (.cv x))))
      (syn_wex y (.all z (syn_wb (.objMem z y) (.objEq z x)))) p0003 p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_csn (.cv x)) (syn_cvv))
      (syn_wex y (.all z (syn_wb (.objMem z y) (.objEq z x)))) p0002 p0006
  have p0008 :=
    @g_vtoclg (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) x
      A (syn_cvv)
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
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      p0001 p0007
  have p0009 := @g_snprc A
  have p0010 :=
    @g_biimpi (.neg (.classMem A (syn_cvv))) (.classEq (syn_csn A) (syn_c0)) p0009
  have p0011 := @g_n_0ex
  have p0012 :=
    @g_syl6eqel (.neg (.classMem A (syn_cvv))) (syn_csn A) (syn_c0) (syn_cvv) p0010 p0011
  have p0013 :=
    @g_pm2_61i (.classMem A (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) p0008 p0012
  exact p0013

@[expose]
noncomputable def g_prex (A : Class) (B : Class) :
    Nominal.NPrf (.classMem (syn_cpr A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cpr A B))
  have p0001 := @g_snex A
  have p0002 := @g_snex B
  have p0003 := @g_unex (syn_csn A) (syn_csn B) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cpr A B) (syn_cun (syn_csn A) (syn_csn B)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_opkex (A : Class) (B : Class) :
    Nominal.NPrf (.classMem (syn_copk A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_copk A B))
  have p0001 := @g_prex (syn_csn A) (syn_cpr A B)
  have p0002 :=
    @g_eqeltri (syn_copk A B) (syn_cpr (syn_csn A) (syn_cpr A B)) (syn_cvv) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_snelpwg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classMem (syn_csn A) (syn_cpw B)) (.classMem A B))) :=
  by
  have p0000 := @g_snssg A B V
  have p0001 := @g_snex A
  have p0002 := @g_elpw (syn_csn A) B p0001
  have p0003 :=
    @g_syl6rbbr (.classMem A V) (.classMem A B) (syn_wss (syn_csn A) B)
      (.classMem (syn_csn A) (syn_cpw B)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_snelpw (A : Class) (B : Class)
    (hyp_snelpw_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_csn A) (syn_cpw B)) (.classMem A B)) :=
  by
  have p0000 := @g_snelpwg A B (syn_cvv)
  have p0001 := Nominal.mp hyp_snelpw_1 p0000
  exact p0001

@[expose]
noncomputable def g_snelpwi (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem (syn_csn A) (syn_cpw B))) :=
  by
  have p0000 := @g_snssi A B
  have p0001 := @g_snex A
  have p0002 := @g_elpw (syn_csn A) B p0001
  have p0003 :=
    @g_sylibr (.classMem A B) (syn_wss (syn_csn A) B) (.classMem (syn_csn A) (syn_cpw B))
      p0000 p0002
  exact p0003

@[expose]
noncomputable def g_unipw (A : Class) :
    Nominal.NPrf (.classEq (syn_cuni (syn_cpw A)) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_eluni y (.cv x) (syn_cpw A)
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
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
  have p0001 := @g_vex y
  have p0002 := @g_elpw (.cv y) A p0001
  have p0003 := @g_ssel (.cv y) A (.cv x)
  have p0004 :=
    @g_sylbi (.classMem (.cv y) (syn_cpw A)) (syn_wss (.cv y) A)
      (.imp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) A)) p0002 p0003
  have p0005 :=
    @g_impcom (.classMem (.cv y) (syn_cpw A)) (.classMem (.cv x) (.cv y))
      (.classMem (.cv x) A) p0004
  have p0006 :=
    @g_exlimiv (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cpw A)))
      (.classMem (.cv x) A) y
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
      p0005
  have p0007 :=
    @g_sylbi (.classMem (.cv x) (syn_cuni (syn_cpw A)))
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (syn_cpw A))))
      (.classMem (.cv x) A) p0000 p0006
  have p0008 := @g_vex x
  have p0009 := @g_snid (.cv x) p0008
  have p0010 := @g_snelpwi (.cv x) A
  have p0011 := @g_elunii (.cv x) (syn_csn (.cv x)) (syn_cpw A)
  have p0012 :=
    @g_sylancr (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn (.cv x)))
      (.classMem (syn_csn (.cv x)) (syn_cpw A)) (.classMem (.cv x) (syn_cuni (syn_cpw A)))
      p0009 p0010 p0011
  have p0013 :=
    @g_impbii (.classMem (.cv x) (syn_cuni (syn_cpw A))) (.classMem (.cv x) A) p0007 p0012
  have p0014 :=
    @g_eqriv x (syn_cuni (syn_cpw A)) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0013
  exact p0014

@[expose]
noncomputable def g_sspwb (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (syn_wss (syn_cpw A) (syn_cpw B))) :=
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
  have p0000 := @g_sstr2 (.cv x) A B
  have p0001 := @g_com12 (syn_wss (.cv x) A) (syn_wss A B) (syn_wss (.cv x) B) p0000
  have p0002 := @g_vex x
  have p0003 := @g_elpw (.cv x) A p0002
  have p0004 := @g_elpw (.cv x) B p0002
  have p0005 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wss (.cv x) A) (syn_wss (.cv x) B)
      (.classMem (.cv x) (syn_cpw A)) (.classMem (.cv x) (syn_cpw B)) p0001 p0003 p0004
  have p0006 :=
    @g_ssrdv (syn_wss A B) x (syn_cpw A) (syn_cpw B)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
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
      p0005
  have p0007 := @g_ssel (syn_cpw A) (syn_cpw B) (syn_csn (.cv x))
  have p0008 := @g_snex (.cv x)
  have p0009 := @g_elpw (syn_csn (.cv x)) A p0008
  have p0010 := @g_snss (.cv x) A p0002
  have p0011 :=
    @g_bitr4i (.classMem (syn_csn (.cv x)) (syn_cpw A)) (syn_wss (syn_csn (.cv x)) A)
      (.classMem (.cv x) A) p0009 p0010
  have p0012 := @g_elpw (syn_csn (.cv x)) B p0008
  have p0013 := @g_snss (.cv x) B p0002
  have p0014 :=
    @g_bitr4i (.classMem (syn_csn (.cv x)) (syn_cpw B)) (syn_wss (syn_csn (.cv x)) B)
      (.classMem (.cv x) B) p0012 p0013
  have p0015 :=
    @g_n_3imtr3g (syn_wss (syn_cpw A) (syn_cpw B))
      (.classMem (syn_csn (.cv x)) (syn_cpw A)) (.classMem (syn_csn (.cv x)) (syn_cpw B))
      (.classMem (.cv x) A) (.classMem (.cv x) B) p0007 p0011 p0014
  have p0016 :=
    @g_ssrdv (syn_wss (syn_cpw A) (syn_cpw B)) x A B
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
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              Finset.mem_union] at ⊢;
            aesop))
      p0015
  have p0017 := @g_impbii (syn_wss A B) (syn_wss (syn_cpw A) (syn_cpw B)) p0006 p0016
  exact p0017

@[expose]
noncomputable def g_pwadjoin (A : Class) (X : Class) (a : Var) (b : Var)
    (dv_A_a : a ∉ A.fv) (dv_A_b : b ∉ A.fv) (dv_X_a : a ∉ X.fv) (dv_X_b : b ∉ X.fv)
    (dv_a_b : a ≠ b) :
    Nominal.NPrf
      (.classEq (syn_cpw (syn_cun A (syn_csn X))) (syn_cun (syn_cpw A) (.cab a
            (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))) :=
  by
  let proofSupport : Finset Var :=
    A.fv ∪ X.fv ∪ ({ a } : Finset Var) ∪ ({ b } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have p0000 := @g_uncom A (syn_csn X)
  have p0001 := @g_sseq2i (syn_cun A (syn_csn X)) (syn_cun (syn_csn X) A) (.cv z) p0000
  have p0002 := @g_ssundif (.cv z) (syn_csn X) A
  have p0003 :=
    @g_bitri (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (syn_wss (.cv z) (syn_cun (syn_csn X) A)) (syn_wss (syn_cdif (.cv z) (syn_csn X)) A)
      p0001 p0002
  have p0004 :=
    @g_biimpi (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (syn_wss (syn_cdif (.cv z) (syn_csn X)) A) p0003
  have p0005 :=
    @g_adantr (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (syn_wss (syn_cdif (.cv z) (syn_csn X)) A) (.classMem X (.cv z)) p0004
  have p0006 := @g_vex z
  have p0007 := @g_snex X
  have p0008 := @g_difex (.cv z) (syn_csn X) p0006 p0007
  have p0009 := @g_elpw (syn_cdif (.cv z) (syn_csn X)) A p0008
  have p0010 :=
    @g_sylibr (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem X (.cv z)))
      (syn_wss (syn_cdif (.cv z) (syn_csn X)) A)
      (.classMem (syn_cdif (.cv z) (syn_csn X)) (syn_cpw A)) p0005 p0009
  have p0011 := @g_difsnid (.cv z) X
  have p0012 :=
    @g_eqcomd (.classMem X (.cv z)) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X))
      (.cv z) p0011
  have p0013 :=
    @g_adantl (.classMem X (.cv z))
      (.classEq (.cv z) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X)))
      (syn_wss (.cv z) (syn_cun A (syn_csn X))) p0012
  have p0014 := @g_uneq1 (.cv b) (syn_cdif (.cv z) (syn_csn X)) (syn_csn X)
  have p0015 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cdif (.cv z) (syn_csn X)))
      (syn_cun (.cv b) (syn_csn X)) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X))
      (.cv z) p0014
  have p0016 :=
    @g_rspcev (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))
      (.classEq (.cv z) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X))) b
      (syn_cdif (.cv z) (syn_csn X)) (syn_cpw A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0015
  have p0017 :=
    @g_syl2anc (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem X (.cv z)))
      (.classMem (syn_cdif (.cv z) (syn_csn X)) (syn_cpw A))
      (.classEq (.cv z) (syn_cun (syn_cdif (.cv z) (syn_csn X)) (syn_csn X)))
      (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0010
      p0013 p0016
  have p0018 :=
    @g_ex (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem X (.cv z))
      (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0017
  have p0019 :=
    @g_con3d (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.classMem X (.cv z))
      (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0018
  have p0020 := @g_ssel (.cv z) (syn_cun A (syn_csn X)) (.cv x)
  have p0021_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wss (.cv z) (syn_cun A (syn_csn X)))
        (.imp (.objMem x z) (.classMem (.cv x) (syn_cun A (syn_csn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cun syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0021 :=
    @g_com12 (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.objMem x z)
      (.classMem (.cv x) (syn_cun A (syn_csn X))) p0021_e00_recanon
  have p0022 := @g_elun (.cv x) A (syn_csn X)
  have p0023 :=
    @g_elsn x X
      (by
        first
        | (aesop))
  have p0024 :=
    @g_orbi2i (.classMem (.cv x) (syn_csn X)) (.classEq (.cv x) X) (.classMem (.cv x) A)
      p0023
  have p0025 :=
    @g_bitri (.classMem (.cv x) (syn_cun A (syn_csn X)))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn X)))
      (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) X)) p0022 p0024
  have p0026 :=
    Nominal.ax1 (.classMem (.cv x) A) (syn_wa (.objMem x z) (.neg (.classMem X (.cv z))))
  have p0027 := @g_eleq1 (.cv x) X (.cv z)
  have p0028_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) X) (syn_wb (.objMem x z) (.classMem X (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0027
  have p0028 :=
    @g_anbi1d (.classEq (.cv x) X) (.objMem x z) (.classMem X (.cv z))
      (.neg (.classMem X (.cv z))) p0028_e00_recanon
  have p0029 := @g_pm2_21 (.classMem X (.cv z)) (.classMem (.cv x) A)
  have p0030 :=
    @g_impcom (.neg (.classMem X (.cv z))) (.classMem X (.cv z)) (.classMem (.cv x) A)
      p0029
  have p0031 :=
    @g_syl6bi (.classEq (.cv x) X) (syn_wa (.objMem x z) (.neg (.classMem X (.cv z))))
      (syn_wa (.classMem X (.cv z)) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A)
      p0028 p0030
  have p0032 :=
    @g_jaoi (.classMem (.cv x) A)
      (.imp (syn_wa (.objMem x z) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A))
      (.classEq (.cv x) X) p0026 p0031
  have p0033 :=
    @g_sylbi (.classMem (.cv x) (syn_cun A (syn_csn X)))
      (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) X))
      (.imp (syn_wa (.objMem x z) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A))
      p0025 p0032
  have p0034 :=
    @g_exp3a (.classMem (.cv x) (syn_cun A (syn_csn X))) (.objMem x z)
      (.neg (.classMem X (.cv z))) (.classMem (.cv x) A) p0033
  have p0035 :=
    @g_com12 (.classMem (.cv x) (syn_cun A (syn_csn X))) (.objMem x z)
      (.imp (.neg (.classMem X (.cv z))) (.classMem (.cv x) A)) p0034
  have p0036 :=
    @g_syld (.objMem x z) (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (.classMem (.cv x) (syn_cun A (syn_csn X)))
      (.imp (.neg (.classMem X (.cv z))) (.classMem (.cv x) A)) p0021 p0035
  have p0037 :=
    @g_imp3a (.objMem x z) (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (.neg (.classMem X (.cv z))) (.classMem (.cv x) A) p0036
  have p0038 :=
    @g_com12 (.objMem x z)
      (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z))))
      (.classMem (.cv x) A) p0037
  have p0039_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z))))
        (.imp (.classMem (.cv x) (.cv z)) (.classMem (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cun syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @g_ssrdv
      (syn_wa (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z)))) x
      (.cv z) A
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
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0039_e00_recanon
  have p0040 :=
    @g_ex (syn_wss (.cv z) (syn_cun A (syn_csn X))) (.neg (.classMem X (.cv z)))
      (syn_wss (.cv z) A) p0039
  have p0041 :=
    @g_syld (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (.neg (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))))
      (.neg (.classMem X (.cv z))) (syn_wss (.cv z) A) p0019 p0040
  have p0042 :=
    @g_orrd (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))))
      (syn_wss (.cv z) A) p0041
  have p0043 :=
    @g_orcomd (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))))
      (syn_wss (.cv z) A) p0042
  have p0044 := @g_ssun3 (.cv z) A (syn_csn X)
  have p0045 := @g_vex b
  have p0046 := @g_elpw (.cv b) A p0045
  have p0047 := @g_unss1 (.cv b) A (syn_csn X)
  have p0048 :=
    @g_sylbi (.classMem (.cv b) (syn_cpw A)) (syn_wss (.cv b) A)
      (syn_wss (syn_cun (.cv b) (syn_csn X)) (syn_cun A (syn_csn X))) p0046 p0047
  have p0049 := @g_sseq1 (.cv z) (syn_cun (.cv b) (syn_csn X)) (syn_cun A (syn_csn X))
  have p0050 :=
    @g_syl5ibrcom (.classMem (.cv b) (syn_cpw A))
      (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))
      (syn_wss (syn_cun (.cv b) (syn_csn X)) (syn_cun A (syn_csn X))) p0048 p0049
  have p0051 :=
    @g_rexlimiv (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))
      (syn_wss (.cv z) (syn_cun A (syn_csn X))) b (syn_cpw A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0050
  have p0052 :=
    @g_jaoi (syn_wss (.cv z) A) (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0044
      p0051
  have p0053 :=
    @g_impbii (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (syn_wo (syn_wss (.cv z) A)
        (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))))
      p0043 p0052
  have p0054 := @g_elpw (.cv z) (syn_cun A (syn_csn X)) p0006
  have p0055 :=
    @g_elun (.cv z) (syn_cpw A)
      (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))
  have p0056 := @g_elpw (.cv z) A p0006
  have p0057 := @g_eqeq1 (.cv a) (.cv z) (syn_cun (.cv b) (syn_csn X))
  have p0058_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a z) (syn_wb (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))
          (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0057
  have p0058 :=
    @g_rexbidv (.objEq a z) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))
      (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X))) b (syn_cpw A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
      p0058_e00_recanon
  have p0059_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv z))
        (syn_wb (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))
          (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cpw, syn_wss, syn_cin,
          syn_ccompl, syn_cnin, syn_wnan, syn_cun, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @g_elab (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))
      (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) a (.cv z)
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
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      p0006 p0059_e01_recanon
  have p0060 :=
    @g_orbi12i (.classMem (.cv z) (syn_cpw A)) (syn_wss (.cv z) A)
      (.classMem (.cv z) (.cab a
          (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))
      (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))) p0056
      p0059
  have p0061 :=
    @g_bitri
      (.classMem (.cv z) (syn_cun (syn_cpw A) (.cab a
            (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))))
      (syn_wo (.classMem (.cv z) (syn_cpw A)) (.classMem (.cv z) (.cab a
            (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))))
      (syn_wo (syn_wss (.cv z) A)
        (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))))
      p0055 p0060
  have p0062 :=
    @g_n_3bitr4i (syn_wss (.cv z) (syn_cun A (syn_csn X)))
      (syn_wo (syn_wss (.cv z) A)
        (syn_wrex b (syn_cpw A) (.classEq (.cv z) (syn_cun (.cv b) (syn_csn X)))))
      (.classMem (.cv z) (syn_cpw (syn_cun A (syn_csn X))))
      (.classMem (.cv z) (syn_cun (syn_cpw A) (.cab a
            (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))))
      p0053 p0054 p0061
  have p0063 :=
    @g_eqriv z (syn_cpw (syn_cun A (syn_csn X)))
      (syn_cun (syn_cpw A) (.cab a
          (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      p0062
  exact p0063

@[expose]
noncomputable def g_preqr1 (A : Class) (B : Class) (C : Class)
    (hyp_preqr1_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_preqr1_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_cpr A C) (syn_cpr B C)) (.classEq A B)) :=
  by
  have p0000 := @g_prid1 A C hyp_preqr1_1
  have p0001 := @g_eleq2 (syn_cpr A C) (syn_cpr B C) A
  have p0002 :=
    @g_mpbii (.classEq (syn_cpr A C) (syn_cpr B C)) (.classMem A (syn_cpr A C))
      (.classMem A (syn_cpr B C)) p0000 p0001
  have p0003 := @g_elpr A B C hyp_preqr1_1
  have p0004 :=
    @g_sylib (.classEq (syn_cpr A C) (syn_cpr B C)) (.classMem A (syn_cpr B C))
      (syn_wo (.classEq A B) (.classEq A C)) p0002 p0003
  have p0005 := @g_prid1 B C hyp_preqr1_2
  have p0006 := @g_eleq2 (syn_cpr A C) (syn_cpr B C) B
  have p0007 :=
    @g_mpbiri (.classEq (syn_cpr A C) (syn_cpr B C)) (.classMem B (syn_cpr A C))
      (.classMem B (syn_cpr B C)) p0005 p0006
  have p0008 := @g_elpr B A C hyp_preqr1_2
  have p0009 :=
    @g_sylib (.classEq (syn_cpr A C) (syn_cpr B C)) (.classMem B (syn_cpr A C))
      (syn_wo (.classEq B A) (.classEq B C)) p0007 p0008
  have p0010 := @g_eqcom A B
  have p0011 := @g_eqeq2 A C B
  have p0012 :=
    @g_oplem1 (.classEq (syn_cpr A C) (syn_cpr B C)) (.classEq A B) (.classEq A C)
      (.classEq B A) (.classEq B C) p0004 p0009 p0010 p0011
  exact p0012

@[expose]
noncomputable def g_preqr2 (A : Class) (B : Class) (C : Class)
    (hyp_preqr2_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_preqr2_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq A B)) :=
  by
  have p0000 := @g_prcom C A
  have p0001 := @g_prcom C B
  have p0002 :=
    @g_eqeq12i (syn_cpr C A) (syn_cpr A C) (syn_cpr C B) (syn_cpr B C) p0000 p0001
  have p0003 := @g_preqr1 A B C hyp_preqr2_1 hyp_preqr2_2
  have p0004 :=
    @g_sylbi (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq (syn_cpr A C) (syn_cpr B C))
      (.classEq A B) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_preqr2g (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (.imp (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_preq2 (.cv x) A C
  have p0001 :=
    @g_eqeq1d (.classEq (.cv x) A) (syn_cpr C (.cv x)) (syn_cpr C A) (syn_cpr C (.cv y))
      p0000
  have p0002 := @g_eqeq1 (.cv x) A (.cv y)
  have p0003_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb (.objEq x y) (.classEq A (.cv y)))) :=
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
      p0002
  have p0003 :=
    @g_imbi12d (.classEq (.cv x) A) (.classEq (syn_cpr C (.cv x)) (syn_cpr C (.cv y)))
      (.classEq (syn_cpr C A) (syn_cpr C (.cv y))) (.objEq x y) (.classEq A (.cv y)) p0001
      p0003_e01_recanon
  have p0004 := @g_preq2 (.cv y) B C
  have p0005 :=
    @g_eqeq2d (.classEq (.cv y) B) (syn_cpr C (.cv y)) (syn_cpr C B) (syn_cpr C A) p0004
  have p0006 := @g_eqeq2 (.cv y) B A
  have p0007 :=
    @g_imbi12d (.classEq (.cv y) B) (.classEq (syn_cpr C A) (syn_cpr C (.cv y)))
      (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq A (.cv y)) (.classEq A B) p0005
      p0006
  have p0008 := @g_vex x
  have p0009 := @g_vex y
  have p0010 := @g_preqr2 (.cv x) (.cv y) C p0008 p0009
  have p0011_e02_recanon :
    Nominal.NPrf (.imp (.classEq (syn_cpr C (.cv x)) (syn_cpr C (.cv y))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0010
  have p0011 :=
    @g_vtocl2g (.imp (.classEq (syn_cpr C (.cv x)) (syn_cpr C (.cv y))) (.objEq x y))
      (.imp (.classEq (syn_cpr C A) (syn_cpr C (.cv y))) (.classEq A (.cv y)))
      (.imp (.classEq (syn_cpr C A) (syn_cpr C B)) (.classEq A B)) x y A B V W
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
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0003 p0007 p0011_e02_recanon
  exact p0011

@[expose]
noncomputable def g_elopk (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_copk B C))
        (syn_wo (.classEq A (syn_csn B)) (.classEq A (syn_cpr B C)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_copk B C))
  have p0001 := @g_eleq2i (syn_copk B C) (syn_cpr (syn_csn B) (syn_cpr B C)) A p0000
  have p0002 := @g_snex B
  have p0003 := @g_prex B C
  have p0004 := @g_elpr2 A (syn_csn B) (syn_cpr B C) p0002 p0003
  have p0005 :=
    @g_bitri (.classMem A (syn_copk B C))
      (.classMem A (syn_cpr (syn_csn B) (syn_cpr B C)))
      (syn_wo (.classEq A (syn_csn B)) (.classEq A (syn_cpr B C))) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_opkth1g (A : Class) (B : Class) (C : Class) (D : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classEq (syn_copk A B) (syn_copk C D))) (.classEq A C)) :=
  by
  have p0000 := @g_eqid (syn_csn C)
  have p0001 :=
    @g_orci (.classEq (syn_csn C) (syn_csn C)) (.classEq (syn_csn C) (syn_cpr C D)) p0000
  have p0002 := @g_elopk (syn_csn C) C D
  have p0003 :=
    @g_mpbir (.classMem (syn_csn C) (syn_copk C D))
      (syn_wo (.classEq (syn_csn C) (syn_csn C)) (.classEq (syn_csn C) (syn_cpr C D)))
      p0001 p0002
  have p0004 := @g_eleq2 (syn_copk A B) (syn_copk C D) (syn_csn C)
  have p0005 :=
    @g_biimprd (.classEq (syn_copk A B) (syn_copk C D))
      (.classMem (syn_csn C) (syn_copk A B)) (.classMem (syn_csn C) (syn_copk C D)) p0004
  have p0006 := @g_elopk (syn_csn C) A B
  have p0007 := @g_snidg A V
  have p0008 := @g_eleq2 (syn_csn C) (syn_csn A) A
  have p0009 :=
    @g_syl5ibrcom (.classMem A V) (.classMem A (syn_csn C))
      (.classEq (syn_csn C) (syn_csn A)) (.classMem A (syn_csn A)) p0007 p0008
  have p0010 := @g_prid1g A B V
  have p0011 := @g_eleq2 (syn_csn C) (syn_cpr A B) A
  have p0012 :=
    @g_syl5ibrcom (.classMem A V) (.classMem A (syn_csn C))
      (.classEq (syn_csn C) (syn_cpr A B)) (.classMem A (syn_cpr A B)) p0010 p0011
  have p0013 :=
    @g_jaod (.classMem A V) (.classEq (syn_csn C) (syn_csn A)) (.classMem A (syn_csn C))
      (.classEq (syn_csn C) (syn_cpr A B)) p0009 p0012
  have p0014 :=
    @g_syl5bi (.classMem (syn_csn C) (syn_copk A B))
      (syn_wo (.classEq (syn_csn C) (syn_csn A)) (.classEq (syn_csn C) (syn_cpr A B)))
      (.classMem A V) (.classMem A (syn_csn C)) p0006 p0013
  have p0015 :=
    @g_sylan9r (.classEq (syn_copk A B) (syn_copk C D))
      (.classMem (syn_csn C) (syn_copk C D)) (.classMem (syn_csn C) (syn_copk A B))
      (.classMem A V) (.classMem A (syn_csn C)) p0005 p0014
  have p0016 :=
    @g_mpi (syn_wa (.classMem A V) (.classEq (syn_copk A B) (syn_copk C D)))
      (.classMem (syn_csn C) (syn_copk C D)) (.classMem A (syn_csn C)) p0003 p0015
  have p0017 := @g_elsncg A C V
  have p0018 :=
    @g_adantr (.classMem A V) (syn_wb (.classMem A (syn_csn C)) (.classEq A C))
      (.classEq (syn_copk A B) (syn_copk C D)) p0017
  have p0019 :=
    @g_mpbid (syn_wa (.classMem A V) (.classEq (syn_copk A B) (syn_copk C D)))
      (.classMem A (syn_csn C)) (.classEq A C) p0016 p0018
  exact p0019

@[expose]
noncomputable def g_opkthg (A : Class) (B : Class) (C : Class) (D : Class) (T : Class)
    (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T))
        (syn_wb (.classEq (syn_copk A B) (syn_copk C D))
          (syn_wa (.classEq A C) (.classEq B D)))) :=
  by
  have p0000 := @g_simp1 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0001 := @g_opkth1g A B C D V
  have p0002 :=
    @g_sylan (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classMem A V)
      (.classEq (syn_copk A B) (syn_copk C D)) (.classEq A C) p0000 p0001
  have p0003 := @g_simp2 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0004 := @g_simp3 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0005 :=
    @g_jca (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classMem B W)
      (.classMem D T) p0003 p0004
  have p0006 := @g_opkeq1 A C B
  have p0007 :=
    @g_eqeq1d (.classEq A C) (syn_copk A B) (syn_copk C B) (syn_copk C D) p0006
  have p0008 :=
    @g_biimpd (.classEq A C) (.classEq (syn_copk A B) (syn_copk C D))
      (.classEq (syn_copk C B) (syn_copk C D)) p0007
  have p0009 :=
    @g_impcom (.classEq A C) (.classEq (syn_copk A B) (syn_copk C D))
      (.classEq (syn_copk C B) (syn_copk C D)) p0008
  have p0010 := (Nominal.classEqRefl (syn_copk C B))
  have p0011 := (Nominal.classEqRefl (syn_copk C D))
  have p0012 :=
    @g_eqeq12i (syn_copk C B) (syn_cpr (syn_csn C) (syn_cpr C B)) (syn_copk C D)
      (syn_cpr (syn_csn C) (syn_cpr C D)) p0010 p0011
  have p0013 := @g_prex C B
  have p0014 := @g_prex C D
  have p0015 := @g_preqr2 (syn_cpr C B) (syn_cpr C D) (syn_csn C) p0013 p0014
  have p0016 :=
    @g_sylbi (.classEq (syn_copk C B) (syn_copk C D))
      (.classEq (syn_cpr (syn_csn C) (syn_cpr C B)) (syn_cpr (syn_csn C) (syn_cpr C D)))
      (.classEq (syn_cpr C B) (syn_cpr C D)) p0012 p0015
  have p0017 := @g_preqr2g B D C W T
  have p0018 :=
    @g_syl5 (.classEq (syn_copk C B) (syn_copk C D))
      (.classEq (syn_cpr C B) (syn_cpr C D)) (syn_wa (.classMem B W) (.classMem D T))
      (.classEq B D) p0016 p0017
  have p0019 :=
    @g_syl5 (syn_wa (.classEq (syn_copk A B) (syn_copk C D)) (.classEq A C))
      (.classEq (syn_copk C B) (syn_copk C D)) (syn_wa (.classMem B W) (.classMem D T))
      (.classEq B D) p0009 p0018
  have p0020 :=
    @g_exp3a (syn_wa (.classMem B W) (.classMem D T))
      (.classEq (syn_copk A B) (syn_copk C D)) (.classEq A C) (.classEq B D) p0019
  have p0021 :=
    @g_imp (syn_wa (.classMem B W) (.classMem D T))
      (.classEq (syn_copk A B) (syn_copk C D)) (.imp (.classEq A C) (.classEq B D)) p0020
  have p0022 :=
    @g_sylan (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T))
      (syn_wa (.classMem B W) (.classMem D T)) (.classEq (syn_copk A B) (syn_copk C D))
      (.imp (.classEq A C) (.classEq B D)) p0005 p0021
  have p0023 :=
    @g_jcai
      (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T))
        (.classEq (syn_copk A B) (syn_copk C D)))
      (.classEq A C) (.classEq B D) p0002 p0022
  have p0024 :=
    @g_ex (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T))
      (.classEq (syn_copk A B) (syn_copk C D)) (syn_wa (.classEq A C) (.classEq B D))
      p0023
  have p0025 := @g_opkeq12 A B C D
  have p0026 :=
    @g_impbid1 (syn_w3a (.classMem A V) (.classMem B W) (.classMem D T))
      (.classEq (syn_copk A B) (syn_copk C D)) (syn_wa (.classEq A C) (.classEq B D))
      p0024 p0025
  exact p0026

@[expose]
noncomputable def g_el1c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_c1c)) (syn_wex x (.classEq A (syn_csn (.cv x))))) :=
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
  have p0000 := @g_elex A (syn_c1c)
  have p0001 := @g_snex (.cv x)
  have p0002 := @g_eleq1 A (syn_csn (.cv x)) (syn_cvv)
  have p0003 :=
    @g_mpbiri (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cvv))
      (.classMem (syn_csn (.cv x)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_exlimiv (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cvv)) x
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
      p0003
  have p0005 := @g_eqeq1 (.cv y) A (syn_csn (.cv x))
  have p0006 :=
    @g_exbidv (.classEq (.cv y) A) (.classEq (.cv y) (syn_csn (.cv x)))
      (.classEq A (syn_csn (.cv x))) x
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
      p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_1c y x
      (by
        first
        | (aesop))
  have p0008 :=
    @g_elab2g (syn_wex x (.classEq (.cv y) (syn_csn (.cv x))))
      (syn_wex x (.classEq A (syn_csn (.cv x)))) y A (syn_c1c) (syn_cvv)
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
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      p0006 p0007
  have p0009 :=
    @g_pm5_21nii (.classMem A (syn_c1c)) (.classMem A (syn_cvv))
      (syn_wex x (.classEq A (syn_csn (.cv x)))) p0000 p0004 p0008
  exact p0009

@[expose]
noncomputable def g_snel1c (A : Class)
    (hyp_snel1c_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_csn A) (syn_c1c)) :=
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
  have p0000 := @g_eqid (syn_csn A)
  have p0001 := @g_sneq (.cv x) A
  have p0002 :=
    @g_eqeq2d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_csn A) p0001
  have p0003 :=
    @g_spcev (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (syn_csn A) (syn_csn A)) x
      A
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_snel1c_1 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 :=
    @g_el1c x (syn_csn A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
  have p0006 :=
    @g_mpbir (.classMem (syn_csn A) (syn_c1c))
      (syn_wex x (.classEq (syn_csn A) (syn_csn (.cv x)))) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_snel1cg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_csn A) (syn_c1c))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_sneq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_c1c) p0000
  have p0002 := @g_vex x
  have p0003 := @g_snel1c (.cv x) p0002
  have p0004 :=
    @g_vtoclg (.classMem (syn_csn (.cv x)) (syn_c1c)) (.classMem (syn_csn A) (syn_c1c)) x
      A V
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
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
              Finset.mem_union] at ⊢;
            aesop))
      p0001 p0003
  exact p0004

@[expose]
noncomputable def g_n_1cex : Nominal.NPrf (.classMem (syn_c1c) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_w_ne_z : w ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have p0000 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.ax1c x y z w
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
  have p0001 :=
    @g_isset x (syn_c1c)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_1c y z
      (by
        first
        | (aesop))
  have p0003 :=
    @g_eqeq2i (syn_c1c) (.cab y (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))) (.cv x)
      p0002
  have p0004 :=
    @g_eqabb (syn_wex z (.classEq (.cv y) (syn_csn (.cv z)))) y (.cv x)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv x) (.cab y (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))))
        (.all y (syn_wb (.objMem y x) (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_bitri (.classEq (.cv x) (syn_c1c))
      (.classEq (.cv x) (.cab y (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))))
      (.all y (syn_wb (.objMem y x) (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))))
      p0003 p0005_e01_recanon
  have p0006 :=
    @g_dfcleq w (.cv y) (syn_csn (.cv z))
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
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton] at ⊢;
            aesop))
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn w (.cv z)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0008_e00_recanon :
    Nominal.NPrf (.classEq (syn_csn (.cv z)) (.cab w (.objEq w z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0007
  have p0008 := @g_eqabri (.objEq w z) w (syn_csn (.cv z)) p0008_e00_recanon
  have p0009 :=
    @g_bibi2i (.classMem (.cv w) (syn_csn (.cv z))) (.objEq w z) (.objMem w y) p0008
  have p0010 :=
    @g_albii (syn_wb (.objMem w y) (.classMem (.cv w) (syn_csn (.cv z))))
      (syn_wb (.objMem w y) (.objEq w z)) w p0009
  have p0011_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv y) (syn_csn (.cv z)))
        (.all w (syn_wb (.objMem w y) (.classMem (.cv w) (syn_csn (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0011 :=
    @g_bitri (.classEq (.cv y) (syn_csn (.cv z)))
      (.all w (syn_wb (.objMem w y) (.classMem (.cv w) (syn_csn (.cv z)))))
      (.all w (syn_wb (.objMem w y) (.objEq w z))) p0011_e00_recanon p0010
  have p0012 :=
    @g_exbii (.classEq (.cv y) (syn_csn (.cv z)))
      (.all w (syn_wb (.objMem w y) (.objEq w z))) z p0011
  have p0013 :=
    @g_bibi2i (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))
      (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z)))) (.objMem y x) p0012
  have p0014 :=
    @g_albii (syn_wb (.objMem y x) (syn_wex z (.classEq (.cv y) (syn_csn (.cv z)))))
      (syn_wb (.objMem y x) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z))))) y
      p0013
  have p0015 :=
    @g_bitri (.classEq (.cv x) (syn_c1c))
      (.all y (syn_wb (.objMem y x) (syn_wex z (.classEq (.cv y) (syn_csn (.cv z))))))
      (.all y (syn_wb (.objMem y x) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z))))))
      p0005 p0014
  have p0016 :=
    @g_exbii (.classEq (.cv x) (syn_c1c))
      (.all y (syn_wb (.objMem y x) (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z))))))
      x p0015
  have p0017 :=
    @g_bitri (.classMem (syn_c1c) (syn_cvv)) (syn_wex x (.classEq (.cv x) (syn_c1c)))
      (syn_wex x (.all y (syn_wb (.objMem y x)
            (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z)))))))
      p0001 p0016
  have p0018 :=
    @g_mpbir (.classMem (syn_c1c) (syn_cvv))
      (syn_wex x (.all y (syn_wb (.objMem y x)
            (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z)))))))
      p0000 p0017
  exact p0018

@[expose]
noncomputable def g_pw1eq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpw1 A) (syn_cpw1 B))) :=
  by
  have p0000 := @g_pweq A B
  have p0001 := @g_ineq1d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_c1c) p0000
  have p0002 := (Nominal.classEqRefl (syn_cpw1 A))
  have p0003 := (Nominal.classEqRefl (syn_cpw1 B))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cin (syn_cpw A) (syn_c1c))
      (syn_cin (syn_cpw B) (syn_c1c)) (syn_cpw1 A) (syn_cpw1 B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_elpw1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 B)) (syn_wrex x B (.classEq A (syn_csn (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := (Nominal.classEqRefl (syn_cpw1 B))
  have p0001 := @g_eleq2i (syn_cpw1 B) (syn_cin (syn_cpw B) (syn_c1c)) A p0000
  have p0002 := @g_elin A (syn_cpw B) (syn_c1c)
  have p0003 :=
    @g_bitri (.classMem A (syn_cpw1 B)) (.classMem A (syn_cin (syn_cpw B) (syn_c1c)))
      (syn_wa (.classMem A (syn_cpw B)) (.classMem A (syn_c1c))) p0001 p0002
  have p0004 :=
    @g_el1c x A
      (by
        first
        | (aesop))
  have p0005 :=
    @g_anbi2i (.classMem A (syn_c1c)) (syn_wex x (.classEq A (syn_csn (.cv x))))
      (.classMem A (syn_cpw B)) p0004
  have p0006 :=
    @g_n_19_42v (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x))) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              Finset.mem_union] at ⊢;
            aesop))
  have p0007 :=
    @g_bitr4i (syn_wa (.classMem A (syn_cpw B)) (.classMem A (syn_c1c)))
      (syn_wa (.classMem A (syn_cpw B)) (syn_wex x (.classEq A (syn_csn (.cv x)))))
      (syn_wex x (syn_wa (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x))))) p0005
      p0006
  have p0008 := @g_eleq1 A (syn_csn (.cv x)) (syn_cpw B)
  have p0009 := @g_snex (.cv x)
  have p0010 := @g_elpw (syn_csn (.cv x)) B p0009
  have p0011 := @g_vex x
  have p0012 := @g_snss (.cv x) B p0011
  have p0013 :=
    @g_bitr4i (.classMem (syn_csn (.cv x)) (syn_cpw B)) (syn_wss (syn_csn (.cv x)) B)
      (.classMem (.cv x) B) p0010 p0012
  have p0014 :=
    @g_syl6bb (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cpw B))
      (.classMem (syn_csn (.cv x)) (syn_cpw B)) (.classMem (.cv x) B) p0008 p0013
  have p0015 :=
    @g_pm5_32ri (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cpw B))
      (.classMem (.cv x) B) p0014
  have p0016 :=
    @g_exbii (syn_wa (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x))))
      (syn_wa (.classMem (.cv x) B) (.classEq A (syn_csn (.cv x)))) x p0015
  have p0017 := (Nominal.biimpRefl (syn_wrex x B (.classEq A (syn_csn (.cv x)))))
  have p0018 :=
    @g_bitr4i
      (syn_wex x (syn_wa (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x)))))
      (syn_wex x (syn_wa (.classMem (.cv x) B) (.classEq A (syn_csn (.cv x)))))
      (syn_wrex x B (.classEq A (syn_csn (.cv x)))) p0016 p0017
  have p0019 :=
    @g_bitri (syn_wa (.classMem A (syn_cpw B)) (.classMem A (syn_c1c)))
      (syn_wex x (syn_wa (.classMem A (syn_cpw B)) (.classEq A (syn_csn (.cv x)))))
      (syn_wrex x B (.classEq A (syn_csn (.cv x)))) p0007 p0018
  have p0020 :=
    @g_bitri (.classMem A (syn_cpw1 B))
      (syn_wa (.classMem A (syn_cpw B)) (.classMem A (syn_c1c)))
      (syn_wrex x B (.classEq A (syn_csn (.cv x)))) p0003 p0019
  exact p0020

@[expose]
noncomputable def g_elpw12 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 B)))
        (syn_wrex x B (.classEq A (syn_csn (syn_csn (.cv x)))))) :=
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
    @g_elpw1 y A (syn_cpw1 B)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1] at ⊢;
            aesop))
  have p0001 :=
    @g_elpw1 x (.cv y) B
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
  have p0002 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 B))
      (syn_wrex x B (.classEq (.cv y) (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))
      p0001
  have p0003 :=
    @g_r19_41v (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))) x B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 B)) (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wrex x B (.classEq (.cv y) (syn_csn (.cv x))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wrex x B
        (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))
      p0002 p0003
  have p0005 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 B)) (.classEq A (syn_csn (.cv y))))
      (syn_wrex x B
        (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))
      y p0004
  have p0006 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1 B) (.classEq A (syn_csn (.cv y)))))
  have p0007 :=
    @g_rexcom4
      (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))) x y B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @g_n_3bitr4i
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 B)) (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wrex x B
          (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))))
      (syn_wrex y (syn_cpw1 B) (.classEq A (syn_csn (.cv y))))
      (syn_wrex x B (syn_wex y
          (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))))
      p0005 p0006 p0007
  have p0009 := @g_snex (.cv x)
  have p0010 := @g_sneq (.cv y) (syn_csn (.cv x))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (.cv x))) (syn_csn (.cv y))
      (syn_csn (syn_csn (.cv x))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (.cv x)))) y
      (syn_csn (.cv x))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0009 p0011
  have p0013 :=
    @g_rexbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (.cv x)))) x B p0012
  have p0014 :=
    @g_n_3bitri (.classMem A (syn_cpw1 (syn_cpw1 B)))
      (syn_wrex y (syn_cpw1 B) (.classEq A (syn_csn (.cv y))))
      (syn_wrex x B (syn_wex y
          (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))))
      (syn_wrex x B (.classEq A (syn_csn (syn_csn (.cv x))))) p0000 p0008 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay
