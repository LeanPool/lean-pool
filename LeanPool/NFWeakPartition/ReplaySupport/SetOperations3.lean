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

/-- Checked nominal proof certificate identified upstream as `g_unisng`. -/
@[expose]
noncomputable def gUnisng (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (synCuni (synCsn A)) A)) :=
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
  have p0000 := @gSneq (.cv x) A
  have p0001 := @gUnieqd (.classEq (.cv x) A) (synCsn (.cv x)) (synCsn A) p0000
  have p0002 := @gId (.classEq (.cv x) A)
  have p0003 :=
    @gEqeq12d (.classEq (.cv x) A) (synCuni (synCsn (.cv x))) (synCuni (synCsn A))
      (.cv x) A p0001 p0002
  have p0004 := @gVex x
  have p0005 := @gUnisn (.cv x) p0004
  have p0006 :=
    @gVtoclg (.classEq (synCuni (synCsn (.cv x))) (.cv x))
      (.classEq (synCuni (synCsn A)) A) x A V
      (by
        aesop)
      (by
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

/-- Checked nominal proof certificate identified upstream as `g_uniun`. -/
@[expose]
noncomputable def gUniun (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCuni (synCun A B)) (synCun (synCuni A) (synCuni B))) :=
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
    @gN1943 (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
      (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)) y
  have p0001 := @gElun (.cv y) A B
  have p0002 :=
    @gAnbi2i (.classMem (.cv y) (synCun A B))
      (synWo (.classMem (.cv y) A) (.classMem (.cv y) B)) (.classMem (.cv x) (.cv y))
      p0001
  have p0003 :=
    @gAndi (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A) (.classMem (.cv y) B)
  have p0004 :=
    @gBitri (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (synCun A B)))
      (synWa (.classMem (.cv x) (.cv y)) (synWo (.classMem (.cv y) A) (.classMem (.cv y) B)))
      (synWo (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
        (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)))
      p0002 p0003
  have p0005 :=
    @gExbii (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (synCun A B)))
      (synWo (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
        (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)))
      y p0004
  have p0006 :=
    @gEluni y (.cv x) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0007 :=
    @gEluni y (.cv x) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0008 :=
    @gOrbi12i (.classMem (.cv x) (synCuni A))
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
      (.classMem (.cv x) (synCuni B))
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))) p0006 p0007
  have p0009 :=
    @gN3bitr4i
      (synWex y (synWo (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
          (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))))
      (synWo (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
        (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B))))
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (synCun A B))))
      (synWo (.classMem (.cv x) (synCuni A)) (.classMem (.cv x) (synCuni B))) p0000
      p0005 p0008
  have p0010 :=
    @gEluni y (.cv x) (synCun A B)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
  have p0011 := @gElun (.cv x) (synCuni A) (synCuni B)
  have p0012 :=
    @gN3bitr4i
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (synCun A B))))
      (synWo (.classMem (.cv x) (synCuni A)) (.classMem (.cv x) (synCuni B)))
      (.classMem (.cv x) (synCuni (synCun A B)))
      (.classMem (.cv x) (synCun (synCuni A) (synCuni B))) p0009 p0010 p0011
  have p0013 :=
    @gEqriv x (synCuni (synCun A B)) (synCun (synCuni A) (synCuni B))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              Finset.mem_union] at ⊢;
            aesop))
      p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_uniss`. -/
@[expose]
noncomputable def gUniss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCuni A) (synCuni B))) :=
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
  have p0000 := @gSsel A B (.cv y)
  have p0001 :=
    @gAnim2d (synWss A B) (.classMem (.cv y) A) (.classMem (.cv y) B)
      (.classMem (.cv x) (.cv y)) p0000
  have p0002 :=
    @gEximdv (synWss A B) (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))
      (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0001
  have p0003 :=
    @gEluni y (.cv x) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0004 :=
    @gEluni y (.cv x) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0005 :=
    @gN3imtr4g (synWss A B)
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) B)))
      (.classMem (.cv x) (synCuni A)) (.classMem (.cv x) (synCuni B)) p0002 p0003 p0004
  have p0006 :=
    @gSsrdv (synWss A B) x (synCuni A) (synCuni B)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ssuni`. -/
@[expose]
noncomputable def gSsuni (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWa (synWss A B) (.classMem B C)) (synWss A (synCuni C))) :=
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
  have p0000 := @gEleq2 (.cv x) B (.cv y)
  have p0001 :=
    @gImbi1d (.classEq (.cv x) B) (.classMem (.cv y) (.cv x)) (.classMem (.cv y) B)
      (.classMem (.cv y) (synCuni C)) p0000
  have p0002 := @gElunii (.cv y) (.cv x) C
  have p0003 :=
    @gExpcom (.classMem (.cv y) (.cv x)) (.classMem (.cv x) C)
      (.classMem (.cv y) (synCuni C)) p0002
  have p0004 :=
    @gVtoclga (.imp (.classMem (.cv y) (.cv x)) (.classMem (.cv y) (synCuni C)))
      (.imp (.classMem (.cv y) B) (.classMem (.cv y) (synCuni C))) x B C
      (by
        aesop)
      (by
        aesop)
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0001 p0003
  have p0005 :=
    @gImim2d (.classMem B C) (.classMem (.cv y) B) (.classMem (.cv y) (synCuni C))
      (.classMem (.cv y) A) p0004
  have p0006 :=
    @gAlimdv (.classMem B C) (.imp (.classMem (.cv y) A) (.classMem (.cv y) B))
      (.imp (.classMem (.cv y) A) (.classMem (.cv y) (synCuni C))) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      p0005
  have p0007 :=
    @gDfss2 y A B
      (by
        aesop)
      (by
        aesop)
  have p0008 :=
    @gDfss2 y A (synCuni C)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni] at ⊢;
            aesop))
  have p0009 :=
    @gN3imtr4g (.classMem B C)
      (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv y) B)))
      (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv y) (synCuni C)))) (synWss A B)
      (synWss A (synCuni C)) p0006 p0007 p0008
  have p0010 := @gImpcom (.classMem B C) (synWss A B) (synWss A (synCuni C)) p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_uni0b`. -/
@[expose]
noncomputable def gUni0b (A : Class) :
    Nominal.NPrf
      (synWb (.classEq (synCuni A) (synC0)) (synWss A (synCsn (synC0)))) :=
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
    @gElsn x (synC0)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
  have p0001 :=
    @gRalbii (.classMem (.cv x) (synCsn (synC0))) (.classEq (.cv x) (synC0)) x A p0000
  have p0002 :=
    @gDfss3 x A (synCsn (synC0))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
  have p0003 :=
    @gNeq0 y (synCuni A)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni] at ⊢;
            aesop))
  have p0004 :=
    @gRexcom4 (.classMem (.cv y) (.cv x)) x y A
      (by
        aesop)
      (by
        aesop)
  have p0005 :=
    @gNeq0 y (.cv x)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 :=
    @gRexbii (.neg (.classEq (.cv x) (synC0))) (synWex y (.classMem (.cv y) (.cv x))) x
      A p0005
  have p0007 :=
    @gEluni2 x (.cv y) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0008 :=
    @gExbii (.classMem (.cv y) (synCuni A)) (synWrex x A (.classMem (.cv y) (.cv x))) y
      p0007
  have p0009 :=
    @gN3bitr4ri (synWrex x A (synWex y (.classMem (.cv y) (.cv x))))
      (synWex y (synWrex x A (.classMem (.cv y) (.cv x))))
      (synWrex x A (.neg (.classEq (.cv x) (synC0))))
      (synWex y (.classMem (.cv y) (synCuni A))) p0004 p0006 p0008
  have p0010 := @gRexnal (.classEq (.cv x) (synC0)) x A
  have p0011 :=
    @gN3bitri (.neg (.classEq (synCuni A) (synC0)))
      (synWex y (.classMem (.cv y) (synCuni A)))
      (synWrex x A (.neg (.classEq (.cv x) (synC0))))
      (.neg (synWral x A (.classEq (.cv x) (synC0)))) p0003 p0009 p0010
  have p0012 :=
    @gCon4bii (.classEq (synCuni A) (synC0)) (synWral x A (.classEq (.cv x) (synC0)))
      p0011
  have p0013 :=
    @gN3bitr4ri (synWral x A (.classMem (.cv x) (synCsn (synC0))))
      (synWral x A (.classEq (.cv x) (synC0))) (synWss A (synCsn (synC0)))
      (.classEq (synCuni A) (synC0)) p0001 p0002 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_uni0`. -/
@[expose]
noncomputable def gUni0 : Nominal.NPrf (.classEq (synCuni (synC0)) (synC0)) :=
  by
  have p0000 := @gN0ss (synCsn (synC0))
  have p0001 := @gUni0b (synC0)
  have p0002 :=
    @gMpbir (.classEq (synCuni (synC0)) (synC0)) (synWss (synC0) (synCsn (synC0)))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elssuni`. -/
@[expose]
noncomputable def gElssuni (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (synWss A (synCuni B))) :=
  by
  have p0000 := @gSsid A
  have p0001 := @gSsuni A A B
  have p0002 := @gMpan (synWss A A) (.classMem A B) (synWss A (synCuni B)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dfint2`. -/
@[expose]
noncomputable def gDfint2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCint A) (.cab x (synWral y A (.classMem (.cv x) (.cv y))))) :=
  by
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfInt x y A
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0001 := (Nominal.biimpRefl (synWral y A (.classMem (.cv x) (.cv y))))
  have p0002 :=
    @gAbbii (synWral y A (.classMem (.cv x) (.cv y)))
      (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))) x p0001
  have p0003_e00_recanon :
    Nominal.NPrf
      (.classEq (synCint A)
        (.cab x (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCint
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
    @gEqtr4i (synCint A)
      (.cab x (.all y (.imp (.classMem (.cv y) A) (.classMem (.cv x) (.cv y)))))
      (.cab x (synWral y A (.classMem (.cv x) (.cv y)))) p0003_e00_recanon p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_inteq`. -/
@[expose]
noncomputable def gInteq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCint A) (synCint B))) :=
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
    @gRaleq (.classMem (.cv x) (.cv y)) y A B
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gAbbidv (.classEq A B) (synWral y A (.classMem (.cv x) (.cv y)))
      (synWral y B (.classMem (.cv x) (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    @gDfint2 x y A
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0003 :=
    @gDfint2 x y B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (.cab x (synWral y A (.classMem (.cv x) (.cv y))))
      (.cab x (synWral y B (.classMem (.cv x) (.cv y)))) (synCint A) (synCint B) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_inteqi`. -/
@[expose]
noncomputable def gInteqi (A : Class) (B : Class)
    (hyp_inteqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCint A) (synCint B)) :=
  by
  have p0000 := @gInteq A B
  have p0001 := Nominal.mp hyp_inteqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elint`. -/
@[expose]
noncomputable def gElint (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_elint_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem A (synCint B))
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
  have p0000 := @gEleq1 (.cv y) A (.cv x)
  have p0001 :=
    @gImbi2d (.classEq (.cv y) A) (.classMem (.cv y) (.cv x)) (.classMem A (.cv x))
      (.classMem (.cv x) B) p0000
  have p0002 :=
    @gAlbidv (.classEq (.cv y) A)
      (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x)))
      (.imp (.classMem (.cv x) B) (.classMem A (.cv x))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfInt y x B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0004_e02_recanon :
    Nominal.NPrf
      (.classEq (synCint B)
        (.cab y (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCint
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
    @gElab2 (.all x (.imp (.classMem (.cv x) B) (.classMem (.cv y) (.cv x))))
      (.all x (.imp (.classMem (.cv x) B) (.classMem A (.cv x)))) y A (synCint B)
      (by
        aesop)
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      hyp_elint_1 p0002 p0004_e02_recanon
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_elint2`. -/
@[expose]
noncomputable def gElint2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_elint2_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem A (synCint B)) (synWral x B (.classMem A (.cv x)))) :=
  by
  have p0000 :=
    @gElint x A B
      (by
        aesop)
      (by
        aesop)
      hyp_elint2_1
  have p0001 := (Nominal.biimpRefl (synWral x B (.classMem A (.cv x))))
  have p0002 :=
    @gBitr4i (.classMem A (synCint B))
      (.all x (.imp (.classMem (.cv x) B) (.classMem A (.cv x))))
      (synWral x B (.classMem A (.cv x))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elintab`. -/
@[expose]
noncomputable def gElintab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_inteqab_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem A (synCint (.cab x ph))) (.all x (.imp ph (.classMem A (.cv x))))) :=
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
    @gElint y A (.cab x ph)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      hyp_inteqab_1
  have p0001 :=
    @gNfsab1 ph x y
      (by
        aesop)
  have p0002 :=
    @gNfv (.classMem A (.cv y)) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gNfim (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y)) x p0001 p0002
  have p0004 :=
    @gNfv (.imp ph (.classMem A (.cv x))) y
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @gEleq1 (.cv y) (.cv x) (.cab x ph)
  have p0006 := @gAbid ph x
  have p0007 :=
    @gSyl6bb (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph))
      (.classMem (.cv x) (.cab x ph)) ph p0005 p0006
  have p0008 := @gEleq2 (.cv y) (.cv x) A
  have p0009 :=
    @gImbi12d (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph)) ph
      (.classMem A (.cv y)) (.classMem A (.cv x)) p0007 p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq y x) (synWb (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y)))
          (.imp ph (.classMem A (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gCbval (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y)))
      (.imp ph (.classMem A (.cv x))) y x p0003 p0004 p0010_e02_recanon
  have p0011 :=
    @gBitri (.classMem A (synCint (.cab x ph)))
      (.all y (.imp (.classMem (.cv y) (.cab x ph)) (.classMem A (.cv y))))
      (.all x (.imp ph (.classMem A (.cv x)))) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_intss1`. -/
@[expose]
noncomputable def gIntss1 (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (synWss (synCint B) A)) :=
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
  have p0000 := @gVex x
  have p0001 :=
    @gElint y (.cv x) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      p0000
  have p0002 := @gEleq1 (.cv y) A B
  have p0003 := @gEleq2 (.cv y) A (.cv x)
  have p0004 :=
    @gImbi12d (.classEq (.cv y) A) (.classMem (.cv y) B) (.classMem A B)
      (.classMem (.cv x) (.cv y)) (.classMem (.cv x) A) p0002 p0003
  have p0005 :=
    @gSpcgv (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y)))
      (.imp (.classMem A B) (.classMem (.cv x) A)) y A B
      (by
        aesop)
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0004
  have p0006 :=
    @gPm243a (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y))))
      (.classMem A B) (.classMem (.cv x) A) p0005
  have p0007 :=
    @gSyl5bi (.classMem (.cv x) (synCint B))
      (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv x) (.cv y)))) (.classMem A B)
      (.classMem (.cv x) A) p0001 p0006
  have p0008 :=
    @gSsrdv (.classMem A B) x (synCint B) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint] at ⊢;
            aesop))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_ssint`. -/
@[expose]
noncomputable def gSsint (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (synWb (synWss A (synCint B)) (synWral x B (synWss A (.cv x)))) :=
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
    @gDfss3 y A (synCint B)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint] at ⊢;
            aesop))
  have p0001 := @gVex y
  have p0002 :=
    @gElint2 x (.cv y) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      p0001
  have p0003 :=
    @gRalbii (.classMem (.cv y) (synCint B)) (synWral x B (.classMem (.cv y) (.cv x)))
      y A p0002
  have p0004 :=
    @gRalcom (.classMem (.cv y) (.cv x)) y x A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0005 :=
    @gDfss3 y A (.cv x)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 :=
    @gRalbii (synWss A (.cv x)) (synWral y A (.classMem (.cv y) (.cv x))) x B p0005
  have p0007 :=
    @gBitr4i (synWral y A (synWral x B (.classMem (.cv y) (.cv x))))
      (synWral x B (synWral y A (.classMem (.cv y) (.cv x))))
      (synWral x B (synWss A (.cv x))) p0004 p0006
  have p0008 :=
    @gN3bitri (synWss A (synCint B)) (synWral y A (.classMem (.cv y) (synCint B)))
      (synWral y A (synWral x B (.classMem (.cv y) (.cv x))))
      (synWral x B (synWss A (.cv x))) p0000 p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_ssintab`. -/
@[expose]
noncomputable def gSsintab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (synWss A (synCint (.cab x ph))) (.all x (.imp ph (synWss A (.cv x))))) :=
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
    @gSsint y A (.cab x ph)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0001 := @gSseq2 (.cv y) (.cv x) A
  have p0002_e00_recanon :
    Nominal.NPrf (.imp (.objEq y x) (synWb (synWss A (.cv y)) (synWss A (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @gRalab2 ph (synWss A (.cv y)) (synWss A (.cv x)) y x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      p0002_e00_recanon
  have p0003 :=
    @gBitri (synWss A (synCint (.cab x ph)))
      (synWral y (.cab x ph) (synWss A (.cv y))) (.all x (.imp ph (synWss A (.cv x))))
      p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ssmin`. -/
@[expose]
noncomputable def gSsmin (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWss A (synCint (.cab x (synWa (synWss A (.cv x)) ph)))) :=
  by
  have p0000 :=
    @gSsintab (synWa (synWss A (.cv x)) ph) x A
      (by
        aesop)
  have p0001 := @gSimpl (synWss A (.cv x)) ph
  have p0002 :=
    @gMpgbir (synWss A (synCint (.cab x (synWa (synWss A (.cv x)) ph))))
      (.imp (synWa (synWss A (.cv x)) ph) (synWss A (.cv x))) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eliun`. -/
@[expose]
noncomputable def gEliun (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (.classMem A (synCiun x B C)) (synWrex x B (.classMem A C))) :=
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
  have p0000 := @gElex A (synCiun x B C)
  have p0001 := @gElex A C
  have p0002 :=
    @gRexlimivw (.classMem A C) (.classMem A (synCvv)) x B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      p0001
  have p0003 := @gEleq1 (.cv y) A C
  have p0004 :=
    @gRexbidv (.classEq (.cv y) A) (.classMem (.cv y) C) (.classMem A C) x B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIun x y B C
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0006 :=
    @gElab2g (synWrex x B (.classMem (.cv y) C)) (synWrex x B (.classMem A C)) y A
      (synCiun x B C) (synCvv)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0004 p0005
  have p0007 :=
    @gPm521nii (.classMem A (synCiun x B C)) (.classMem A (synCvv))
      (synWrex x B (.classMem A C)) p0000 p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ss2iun`. -/
@[expose]
noncomputable def gSs2iun (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWral x A (synWss B C)) (synWss (synCiun x A B) (synCiun x A C))) :=
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
  have p0000 := @gSsel B C (.cv y)
  have p0001 :=
    @gRalimi (synWss B C) (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)) x A p0000
  have p0002 := @gRexim (.classMem (.cv y) B) (.classMem (.cv y) C) x A
  have p0003 :=
    @gSyl (synWral x A (synWss B C))
      (synWral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)))
      (.imp (synWrex x A (.classMem (.cv y) B)) (synWrex x A (.classMem (.cv y) C)))
      p0001 p0002
  have p0004 :=
    @gEliun x (.cv y) A B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gEliun x (.cv y) A C
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 :=
    @gN3imtr4g (synWral x A (synWss B C)) (synWrex x A (.classMem (.cv y) B))
      (synWrex x A (.classMem (.cv y) C)) (.classMem (.cv y) (synCiun x A B))
      (.classMem (.cv y) (synCiun x A C)) p0003 p0004 p0005
  have p0007 :=
    @gSsrdv (synWral x A (synWss B C)) y (synCiun x A B) (synCiun x A C)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_iuneq2`. -/
@[expose]
noncomputable def gIuneq2 (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWral x A (.classEq B C)) (.classEq (synCiun x A B) (synCiun x A C))) :=
  by
  have p0000 := @gSs2iun x A B C
  have p0001 := @gSs2iun x A C B
  have p0002 :=
    @gAnim12i (synWral x A (synWss B C)) (synWss (synCiun x A B) (synCiun x A C))
      (synWral x A (synWss C B)) (synWss (synCiun x A C) (synCiun x A B)) p0000 p0001
  have p0003 := @gEqss B C
  have p0004 := @gRalbii (.classEq B C) (synWa (synWss B C) (synWss C B)) x A p0003
  have p0005 := @gR1926 (synWss B C) (synWss C B) x A
  have p0006 :=
    @gBitri (synWral x A (.classEq B C))
      (synWral x A (synWa (synWss B C) (synWss C B)))
      (synWa (synWral x A (synWss B C)) (synWral x A (synWss C B))) p0004 p0005
  have p0007 := @gEqss (synCiun x A B) (synCiun x A C)
  have p0008 :=
    @gN3imtr4i (synWa (synWral x A (synWss B C)) (synWral x A (synWss C B)))
      (synWa (synWss (synCiun x A B) (synCiun x A C))
        (synWss (synCiun x A C) (synCiun x A B)))
      (synWral x A (.classEq B C)) (.classEq (synCiun x A B) (synCiun x A C)) p0002
      p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_iuneq2i`. -/
@[expose]
noncomputable def gIuneq2i (x : Var) (A : Class) (B : Class) (C : Class)
    (hyp_iuneq2i_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.classEq B C))) :
    Nominal.NPrf (.classEq (synCiun x A B) (synCiun x A C)) :=
  by
  have p0000 := @gIuneq2 x A B C
  have p0001 :=
    @gMprg (.classEq B C) (.classEq (synCiun x A B) (synCiun x A C)) x A p0000
      hyp_iuneq2i_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfiun`. -/
@[expose]
noncomputable def gNfiun (x : Var) (y : Var) (A : Class) (B : Class)
    (hyp_nfiun_1 : Nominal.NPrf (synWnfc y A))
    (hyp_nfiun_2 : Nominal.NPrf (synWnfc y B)) :
    Nominal.NPrf (synWnfc y (synCiun x A B)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIun x z A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gNfcri y z B
      (by
        aesop)
      hyp_nfiun_2
  have p0002 := @gNfrex (.classMem (.cv z) B) y x A hyp_nfiun_1 p0001
  have p0003 := @gNfab (synWrex x A (.classMem (.cv z) B)) y z p0002
  have p0004 :=
    @gNfcxfr y (synCiun x A B) (.cab z (synWrex x A (.classMem (.cv z) B))) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfiu1`. -/
@[expose]
noncomputable def gNfiu1 (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf (synWnfc x (synCiun x A B)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIun x y A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0001 := @gNfre1 (.classMem (.cv y) B) x A
  have p0002 := @gNfab (synWrex x A (.classMem (.cv y) B)) x y p0001
  have p0003 :=
    @gNfcxfr x (synCiun x A B) (.cab y (synWrex x A (.classMem (.cv y) B))) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_dfiun2g`. -/
@[expose]
noncomputable def gDfiun2g (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWral x A (.classMem B C)) (.classEq (synCiun x A B)
          (synCuni (.cab y (synWrex x A (.classEq (.cv y) B)))))) :=
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
  have p0000 := @gNfra1 (.classMem B C) x A
  have p0001 := @gRsp (.classMem B C) x A
  have p0002 :=
    @gClel3g y (.cv z) B C
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0003 :=
    @gSyl6 (synWral x A (.classMem B C)) (.classMem (.cv x) A) (.classMem B C)
      (synWb (.classMem (.cv z) B)
        (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      p0001 p0002
  have p0004 :=
    @gImp (synWral x A (.classMem B C)) (.classMem (.cv x) A)
      (synWb (.classMem (.cv z) B)
        (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      p0003
  have p0005 :=
    @gRexbida (synWral x A (.classMem B C)) (.classMem (.cv z) B)
      (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))) x A p0000
      p0004
  have p0006 :=
    @gRexcom4 (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))) x y A
      (by
        aesop)
      (by
        aesop)
  have p0007 :=
    @gSyl6bb (synWral x A (.classMem B C)) (synWrex x A (.classMem (.cv z) B))
      (synWrex x A (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      (synWex y (synWrex x A (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      p0005 p0006
  have p0008 :=
    @gR1941v (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)) x A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0009 :=
    @gExbii (synWrex x A (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y))))
      (synWa (synWrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y))) y p0008
  have p0010 :=
    @gExancom (synWrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y)) y
  have p0011 :=
    @gBitri
      (synWex y (synWrex x A (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      (synWex y (synWa (synWrex x A (.classEq (.cv y) B)) (.classMem (.cv z) (.cv y))))
      (synWex y (synWa (.classMem (.cv z) (.cv y)) (synWrex x A (.classEq (.cv y) B))))
      p0009 p0010
  have p0012 :=
    @gSyl6bb (synWral x A (.classMem B C)) (synWrex x A (.classMem (.cv z) B))
      (synWex y (synWrex x A (synWa (.classEq (.cv y) B) (.classMem (.cv z) (.cv y)))))
      (synWex y (synWa (.classMem (.cv z) (.cv y)) (synWrex x A (.classEq (.cv y) B))))
      p0007 p0011
  have p0013 :=
    @gEliun x (.cv z) A B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0014 :=
    @gEluniab (synWrex x A (.classEq (.cv y) B)) y (.cv z)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0015 :=
    @gN3bitr4g (synWral x A (.classMem B C)) (synWrex x A (.classMem (.cv z) B))
      (synWex y (synWa (.classMem (.cv z) (.cv y)) (synWrex x A (.classEq (.cv y) B))))
      (.classMem (.cv z) (synCiun x A B))
      (.classMem (.cv z) (synCuni (.cab y (synWrex x A (.classEq (.cv y) B))))) p0012
      p0013 p0014
  have p0016 :=
    @gEqrdv (synWral x A (.classMem B C)) z (synCiun x A B)
      (synCuni (.cab y (synWrex x A (.classEq (.cv y) B))))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
              Finset.mem_union, Finset.mem_erase] at ⊢;
            aesop))
      (by
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
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_dfiun2`. -/
@[expose]
noncomputable def gDfiun2 (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_dfiun2_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.classEq (synCiun x A B) (synCuni (.cab y (synWrex x A (.classEq (.cv y) B))))) :=
  by
  have p0000 :=
    @gDfiun2g x y A B (synCvv)
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0001 := @gA1i (.classMem B (synCvv)) (.classMem (.cv x) A) hyp_dfiun2_1
  have p0002 :=
    @gMprg (.classMem B (synCvv))
      (.classEq (synCiun x A B) (synCuni (.cab y (synWrex x A (.classEq (.cv y) B)))))
      x A p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbviun`. -/
@[expose]
noncomputable def gCbviun (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbviun_1 : Nominal.NPrf (synWnfc y B))
    (hyp_cbviun_2 : Nominal.NPrf (synWnfc x C))
    (hyp_cbviun_3 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (synCiun x A B) (synCiun y A C)) :=
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
    @gNfcri y z B
      (by
        aesop)
      hyp_cbviun_1
  have p0001 :=
    @gNfcri x z C
      (by
        aesop)
      hyp_cbviun_2
  have p0002_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.classEq B C)) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_cbviun_3
  have p0002 := @gEleq2d (.classEq (.cv x) (.cv y)) B C (.cv z) p0002_e00_recanon
  have p0003_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (.classMem (.cv z) B) (.classMem (.cv z) C))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @gCbvrex (.classMem (.cv z) B) (.classMem (.cv z) C) x y A
      (by
        aesop)
      (by
        aesop)
      p0000 p0001 p0003_e02_recanon
  have p0004 :=
    @gAbbii (synWrex x A (.classMem (.cv z) B)) (synWrex y A (.classMem (.cv z) C)) z
      p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIun x z A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIun y z A C
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0007 :=
    @gN3eqtr4i (.cab z (synWrex x A (.classMem (.cv z) B)))
      (.cab z (synWrex y A (.classMem (.cv z) C))) (synCiun x A B) (synCiun y A C)
      p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_iunss`. -/
@[expose]
noncomputable def gIunss (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (synWb (synWss (synCiun x A B) C) (synWral x A (synWss B C))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIun x y A B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gSseq1i (synCiun x A B) (.cab y (synWrex x A (.classMem (.cv y) B))) C p0000
  have p0002 :=
    @gAbss (synWrex x A (.classMem (.cv y) B)) y C
      (by
        aesop)
  have p0003 :=
    @gDfss2 y B C
      (by
        aesop)
      (by
        aesop)
  have p0004 :=
    @gRalbii (synWss B C) (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))) x
      A p0003
  have p0005 :=
    @gRalcom4 (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)) x y A
      (by
        aesop)
      (by
        aesop)
  have p0006 :=
    @gR1923v (.classMem (.cv y) B) (.classMem (.cv y) C) x A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0007 :=
    @gAlbii (synWral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C)))
      (.imp (synWrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C)) y p0006
  have p0008 :=
    @gN3bitrri (synWral x A (synWss B C))
      (synWral x A (.all y (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))))
      (.all y (synWral x A (.imp (.classMem (.cv y) B) (.classMem (.cv y) C))))
      (.all y (.imp (synWrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C))) p0004
      p0005 p0007
  have p0009 :=
    @gN3bitri (synWss (synCiun x A B) C)
      (synWss (.cab y (synWrex x A (.classMem (.cv y) B))) C)
      (.all y (.imp (synWrex x A (.classMem (.cv y) B)) (.classMem (.cv y) C)))
      (synWral x A (synWss B C)) p0001 p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_iunab`. -/
@[expose]
noncomputable def gIunab (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (synCiun x A (.cab y ph)) (.cab y (synWrex x A ph))) :=
  by
  have p0000 :=
    @gNfcv y A
      (by
        aesop)
  have p0001 := @gNfab1 ph y
  have p0002 := @gNfiun x y A (.cab y ph) p0000 p0001
  have p0003 := @gNfab1 (synWrex x A ph) y
  have p0004 :=
    @gCleqf y (synCiun x A (.cab y ph)) (.cab y (synWrex x A ph)) p0002 p0003
  have p0005 := @gAbid ph y
  have p0006 := @gRexbii (.classMem (.cv y) (.cab y ph)) ph x A p0005
  have p0007 :=
    @gEliun x (.cv y) A (.cab y ph)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0008 := @gAbid (synWrex x A ph) y
  have p0009 :=
    @gN3bitr4i (synWrex x A (.classMem (.cv y) (.cab y ph))) (synWrex x A ph)
      (.classMem (.cv y) (synCiun x A (.cab y ph)))
      (.classMem (.cv y) (.cab y (synWrex x A ph))) p0006 p0007 p0008
  have p0010 :=
    @gMpgbir (.classEq (synCiun x A (.cab y ph)) (.cab y (synWrex x A ph)))
      (synWb (.classMem (.cv y) (synCiun x A (.cab y ph)))
        (.classMem (.cv y) (.cab y (synWrex x A ph))))
      y p0004 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_iunid`. -/
@[expose]
noncomputable def gIunid (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCiun x A (synCsn (.cv x))) A) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn y (.cv x)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 := @gEqucom y x
  have p0002_e00_recanon :
    Nominal.NPrf (synWb (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gAbbii (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y)) y p0002_e00_recanon
  have p0003 :=
    @gEqtri (synCsn (.cv x)) (.cab y (.classEq (.cv y) (.cv x)))
      (.cab y (.classEq (.cv x) (.cv y))) p0000 p0002
  have p0004 :=
    @gA1i (.classEq (synCsn (.cv x)) (.cab y (.classEq (.cv x) (.cv y))))
      (.classMem (.cv x) A) p0003
  have p0005 := @gIuneq2i x A (synCsn (.cv x)) (.cab y (.classEq (.cv x) (.cv y))) p0004
  have p0006 :=
    @gIunab (.classEq (.cv x) (.cv y)) x y A
      (by
        aesop)
      (by
        aesop)
  have p0007 :=
    @gRisset x (.cv y) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0008 :=
    @gAbbii (.classMem (.cv y) A) (synWrex x A (.classEq (.cv x) (.cv y))) y p0007
  have p0009 :=
    @gAbid2 y A
      (by
        aesop)
  have p0010 :=
    @gN3eqtr2i (synCiun x A (.cab y (.classEq (.cv x) (.cv y))))
      (.cab y (synWrex x A (.classEq (.cv x) (.cv y)))) (.cab y (.classMem (.cv y) A)) A
      p0006 p0008 p0009
  have p0011 :=
    @gEqtri (synCiun x A (synCsn (.cv x)))
      (synCiun x A (.cab y (.classEq (.cv x) (.cv y)))) A p0005 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_opkeq1`. -/
@[expose]
noncomputable def gOpkeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCopk A C) (synCopk B C))) :=
  by
  have p0000 := @gSneq A B
  have p0001 := @gPreq1 A B C
  have p0002 :=
    @gPreq12d (.classEq A B) (synCsn A) (synCsn B) (synCpr A C) (synCpr B C) p0000
      p0001
  have p0003 := (Nominal.classEqRefl (synCopk A C))
  have p0004 := (Nominal.classEqRefl (synCopk B C))
  have p0005 :=
    @gN3eqtr4g (.classEq A B) (synCpr (synCsn A) (synCpr A C))
      (synCpr (synCsn B) (synCpr B C)) (synCopk A C) (synCopk B C) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_opkeq2`. -/
@[expose]
noncomputable def gOpkeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCopk C A) (synCopk C B))) :=
  by
  have p0000 := @gPreq2 A B C
  have p0001 := @gPreq2d (.classEq A B) (synCpr C A) (synCpr C B) (synCsn C) p0000
  have p0002 := (Nominal.classEqRefl (synCopk C A))
  have p0003 := (Nominal.classEqRefl (synCopk C B))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCpr (synCsn C) (synCpr C A))
      (synCpr (synCsn C) (synCpr C B)) (synCopk C A) (synCopk C B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_opkeq12`. -/
@[expose]
noncomputable def gOpkeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A C) (.classEq B D)) (.classEq (synCopk A B) (synCopk C D))) :=
  by
  have p0000 := @gOpkeq1 A C B
  have p0001 := @gOpkeq2 B D C
  have p0002 :=
    @gSylan9eq (.classEq A C) (.classEq B D) (synCopk A B) (synCopk C B) (synCopk C D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_opkeq2i`. -/
@[expose]
noncomputable def gOpkeq2i (A : Class) (B : Class) (C : Class)
    (hyp_opkeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCopk C A) (synCopk C B)) :=
  by
  have p0000 := @gOpkeq2 A B C
  have p0001 := Nominal.mp hyp_opkeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opkeq1d`. -/
@[expose]
noncomputable def gOpkeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCopk A C) (synCopk B C))) :=
  by
  have p0000 := @gOpkeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCopk A C) (synCopk B C)) hyp_opkeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opkeq2d`. -/
@[expose]
noncomputable def gOpkeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCopk C A) (synCopk C B))) :=
  by
  have p0000 := @gOpkeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCopk C A) (synCopk C B)) hyp_opkeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opkeq12d`. -/
@[expose]
noncomputable def gOpkeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_opkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_opkeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCopk A C) (synCopk B D))) :=
  by
  have p0000 := @gOpkeq12 A C B D
  have p0001 :=
    @gSyl2anc ph (.classEq A B) (.classEq C D) (.classEq (synCopk A C) (synCopk B D))
      hyp_opkeq1d_1 hyp_opkeq12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_compldif`. -/
@[expose]
noncomputable def gCompldif (A : Class) :
    Nominal.NPrf (.classEq (synCcompl A) (synCdif (synCvv) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCdif (synCvv) A))
  have p0001 := @gIncom (synCvv) (synCcompl A)
  have p0002 := @gInv1 (synCcompl A)
  have p0003 :=
    @gN3eqtrri (synCdif (synCvv) A) (synCin (synCvv) (synCcompl A))
      (synCin (synCcompl A) (synCvv)) (synCcompl A) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_complV`. -/
@[expose]
noncomputable def gComplV : Nominal.NPrf (.classEq (synCcompl (synCvv)) (synC0)) :=
  by
  have p0000 := @gCompldif (synCvv)
  have p0001 := (Nominal.classEqRefl (synC0))
  have p0002 :=
    @gEqtr4i (synCcompl (synCvv)) (synCdif (synCvv) (synCvv)) (synC0) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nincompl`. -/
@[expose]
noncomputable def gNincompl (A : Class) :
    Nominal.NPrf (.classEq (synCnin A (synCcompl A)) (synCvv)) :=
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
    @gEqv x (synCnin A (synCcompl A))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
              Finset.mem_union] at ⊢;
            aesop))
  have p0001 := @gPm324 (.classMem (.cv x) A)
  have p0002 := @gVex x
  have p0003 := @gElnin (.cv x) A (synCcompl A) p0002
  have p0004 := @gElcompl (.cv x) A p0002
  have p0005 :=
    @gNanbi2i (.classMem (.cv x) (synCcompl A)) (.neg (.classMem (.cv x) A))
      (.classMem (.cv x) A) p0004
  have p0006 :=
    (Nominal.biimpRefl (synWnan (.classMem (.cv x) A) (.neg (.classMem (.cv x) A))))
  have p0007 :=
    @gN3bitri (.classMem (.cv x) (synCnin A (synCcompl A)))
      (synWnan (.classMem (.cv x) A) (.classMem (.cv x) (synCcompl A)))
      (synWnan (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))
      (.neg (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))) p0003 p0005 p0006
  have p0008 :=
    @gMpbir (.classMem (.cv x) (synCnin A (synCcompl A)))
      (.neg (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) A)))) p0001 p0007
  have p0009 :=
    @gMpgbir (.classEq (synCnin A (synCcompl A)) (synCvv))
      (.classMem (.cv x) (synCnin A (synCcompl A))) x p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_incompl`. -/
@[expose]
noncomputable def gIncompl (A : Class) :
    Nominal.NPrf (.classEq (synCin A (synCcompl A)) (synC0)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCin A (synCcompl A)))
  have p0001 := @gNincompl A
  have p0002 := @gCompleqi (synCnin A (synCcompl A)) (synCvv) p0001
  have p0003 := @gComplV
  have p0004 :=
    @gN3eqtri (synCin A (synCcompl A)) (synCcompl (synCnin A (synCcompl A)))
      (synCcompl (synCvv)) (synC0) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_uncompl`. -/
@[expose]
noncomputable def gUncompl (A : Class) :
    Nominal.NPrf (.classEq (synCun A (synCcompl A)) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCun A (synCcompl A)))
  have p0001 := @gNincompl (synCcompl A)
  have p0002 :=
    @gEqtri (synCun A (synCcompl A))
      (synCnin (synCcompl A) (synCcompl (synCcompl A))) (synCvv) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_inindif`. -/
@[expose]
noncomputable def gInindif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCin (synCin A B) (synCdif A B)) (synC0)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCdif A B))
  have p0001 := @gIneq2i (synCdif A B) (synCin A (synCcompl B)) (synCin A B) p0000
  have p0002 := @gInindi A B (synCcompl B)
  have p0003 := @gIncompl B
  have p0004 := @gIneq2i (synCin B (synCcompl B)) (synC0) A p0003
  have p0005 := @gIn0 A
  have p0006 :=
    @gEqtri (synCin A (synCin B (synCcompl B))) (synCin A (synC0)) (synC0) p0004
      p0005
  have p0007 :=
    @gN3eqtr2i (synCin (synCin A B) (synCdif A B))
      (synCin (synCin A B) (synCin A (synCcompl B)))
      (synCin A (synCin B (synCcompl B))) (synC0) p0001 p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ssofss`. -/
@[expose]
noncomputable def gSsofss (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (.imp (synWss A C) (synWb (synWss A B)
          (synWral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))))) :=
  by
  have p0000 := @gVex x
  have p0001 := @gElcompl (.cv x) C p0000
  have p0002 := @gSsel A C (.cv x)
  have p0003 := @gCon3d (synWss A C) (.classMem (.cv x) A) (.classMem (.cv x) C) p0002
  have p0004 :=
    @gSyl5bi (.classMem (.cv x) (synCcompl C)) (.neg (.classMem (.cv x) C))
      (synWss A C) (.neg (.classMem (.cv x) A)) p0001 p0003
  have p0005 :=
    @gImp (synWss A C) (.classMem (.cv x) (synCcompl C)) (.neg (.classMem (.cv x) A))
      p0004
  have p0006 :=
    @gPm221d (synWa (synWss A C) (.classMem (.cv x) (synCcompl C)))
      (.classMem (.cv x) A) (.classMem (.cv x) B) p0005
  have p0007 :=
    @gRalrimiva (synWss A C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      (synCcompl C)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0006
  have p0008 :=
    @gBiantrud (synWss A C)
      (synWral x (synCcompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) p0007
  have p0009 := @gRalv (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
  have p0010 := @gUncompl C
  have p0011 :=
    @gRaleqi (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      (synCun C (synCcompl C)) (synCvv)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      p0010
  have p0012 :=
    @gDfss2 x A B
      (by
        aesop)
      (by
        aesop)
  have p0013 :=
    @gN3bitr4ri
      (synWral x (synCvv) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWral x (synCun C (synCcompl C)) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWss A B) p0009 p0011 p0012
  have p0014 :=
    @gRalunb (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) x C (synCcompl C)
  have p0015 :=
    @gBitri (synWss A B)
      (synWral x (synCun C (synCcompl C)) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWa (synWral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (synWral x (synCcompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))))
      p0013 p0014
  have p0016 :=
    @gSyl6rbbr (synWss A C)
      (synWral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (synWa (synWral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (synWral x (synCcompl C) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))))
      (synWss A B) p0008 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_ssofeq`. -/
@[expose]
noncomputable def gSsofeq (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (.imp (synWa (synWss A C) (synWss B C)) (synWb (.classEq A B)
          (synWral x C (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))))) :=
  by
  have p0000 :=
    @gSsofss x A B C
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gSsofss x B A C
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0002 :=
    @gBi2anan9 (synWss A C) (synWss A B)
      (synWral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))) (synWss B C)
      (synWss B A) (synWral x C (.imp (.classMem (.cv x) B) (.classMem (.cv x) A)))
      p0000 p0001
  have p0003 := @gEqss A B
  have p0004 := @gRalbiim (.classMem (.cv x) A) (.classMem (.cv x) B) x C
  have p0005 :=
    @gN3bitr4g (synWa (synWss A C) (synWss B C)) (synWa (synWss A B) (synWss B A))
      (synWa (synWral x C (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
        (synWral x C (.imp (.classMem (.cv x) B) (.classMem (.cv x) A))))
      (.classEq A B) (synWral x C (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_axprimlem1`. -/
@[expose]
noncomputable def gAxprimlem1 (B : Class) (a : Var) (c : Var) (dv_B_c : c ∉ B.fv)
    (dv_a_c : a ≠ c) :
    Nominal.NPrf
      (synWb (.classEq (.cv a) (synCsn B))
        (.all c (synWb (.objMem c a) (.classEq (.cv c) B)))) :=
  by
  have p0000 :=
    @gDfcleq c (.cv a) (synCsn B)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
  have p0001 :=
    @gElsn c B
      (by
        aesop)
  have p0002 :=
    @gBibi2i (.classMem (.cv c) (synCsn B)) (.classEq (.cv c) B) (.objMem c a) p0001
  have p0003 :=
    @gAlbii (synWb (.objMem c a) (.classMem (.cv c) (synCsn B)))
      (synWb (.objMem c a) (.classEq (.cv c) B)) c p0002
  have p0004_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv a) (synCsn B))
        (.all c (synWb (.objMem c a) (.classMem (.cv c) (synCsn B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
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
    @gBitri (.classEq (.cv a) (synCsn B))
      (.all c (synWb (.objMem c a) (.classMem (.cv c) (synCsn B))))
      (.all c (synWb (.objMem c a) (.classEq (.cv c) B))) p0004_e00_recanon p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ninexg`. -/
@[expose]
noncomputable def gNinexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCnin A B) (synCvv))) :=
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
  have p0000 := @gNineq1 (.cv x) A (.cv y)
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCnin (.cv x) (.cv y)) (synCnin A (.cv y))
      (synCvv) p0000
  have p0002 := @gNineq2 (.cv y) B A
  have p0003 :=
    @gEleq1d (.classEq (.cv y) B) (synCnin A (.cv y)) (synCnin A B) (synCvv) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axNin x y z w
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
  have p0005 :=
    @gIsset z (synCnin (.cv x) (.cv y))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 :=
    @gDfcleq w (.cv z) (synCnin (.cv x) (.cv y))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0007 := @gVex w
  have p0008 := @gElnin (.cv w) (.cv x) (.cv y) p0007
  have p0009_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv w) (synCnin (.cv x) (.cv y)))
        (synWnan (.objMem w x) (.objMem w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCnin synWnan synWa
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
    @gBibi2i (.classMem (.cv w) (synCnin (.cv x) (.cv y)))
      (synWnan (.objMem w x) (.objMem w y)) (.objMem w z) p0009_e00_recanon
  have p0010 :=
    @gAlbii (synWb (.objMem w z) (.classMem (.cv w) (synCnin (.cv x) (.cv y))))
      (synWb (.objMem w z) (synWnan (.objMem w x) (.objMem w y))) w p0009
  have p0011_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv z) (synCnin (.cv x) (.cv y)))
        (.all w (synWb (.objMem w z) (.classMem (.cv w) (synCnin (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCnin synWnan synWa
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
    @gBitri (.classEq (.cv z) (synCnin (.cv x) (.cv y)))
      (.all w (synWb (.objMem w z) (.classMem (.cv w) (synCnin (.cv x) (.cv y)))))
      (.all w (synWb (.objMem w z) (synWnan (.objMem w x) (.objMem w y))))
      p0011_e00_recanon p0010
  have p0012 :=
    @gExbii (.classEq (.cv z) (synCnin (.cv x) (.cv y)))
      (.all w (synWb (.objMem w z) (synWnan (.objMem w x) (.objMem w y)))) z p0011
  have p0013 :=
    @gBitri (.classMem (synCnin (.cv x) (.cv y)) (synCvv))
      (synWex z (.classEq (.cv z) (synCnin (.cv x) (.cv y))))
      (synWex z (.all w (synWb (.objMem w z) (synWnan (.objMem w x) (.objMem w y)))))
      p0005 p0012
  have p0014 :=
    @gMpbir (.classMem (synCnin (.cv x) (.cv y)) (synCvv))
      (synWex z (.all w (synWb (.objMem w z) (synWnan (.objMem w x) (.objMem w y)))))
      p0004 p0013
  have p0015 :=
    @gVtocl2g (.classMem (synCnin (.cv x) (.cv y)) (synCvv))
      (.classMem (synCnin A (.cv y)) (synCvv)) (.classMem (synCnin A B) (synCvv)) x y
      A B V W
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
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnin,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      (by
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

/-- Checked nominal proof certificate identified upstream as `g_complexg`. -/
@[expose]
noncomputable def gComplexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCcompl A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCcompl A))
  have p0001 := @gNinexg A A V V
  have p0002 := @gAnidms (.classMem A V) (.classMem (synCnin A A) (synCvv)) p0001
  have p0003 :=
    @gSyl5eqel (.classMem A V) (synCcompl A) (synCnin A A) (synCvv) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_inexg`. -/
@[expose]
noncomputable def gInexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCin A B) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCin A B))
  have p0001 := @gNinexg A B V W
  have p0002 := @gComplexg (synCnin A B) (synCvv)
  have p0003 :=
    @gSyl (synWa (.classMem A V) (.classMem B W)) (.classMem (synCnin A B) (synCvv))
      (.classMem (synCcompl (synCnin A B)) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCin A B)
      (synCcompl (synCnin A B)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_unexg`. -/
@[expose]
noncomputable def gUnexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCun A B) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCun A B))
  have p0001 := @gComplexg A V
  have p0002 := @gComplexg B W
  have p0003 := @gNinexg (synCcompl A) (synCcompl B) (synCvv) (synCvv)
  have p0004 :=
    @gSyl2an (.classMem A V) (.classMem (synCcompl A) (synCvv))
      (.classMem (synCcompl B) (synCvv))
      (.classMem (synCnin (synCcompl A) (synCcompl B)) (synCvv)) (.classMem B W) p0001
      p0002 p0003
  have p0005 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCun A B)
      (synCnin (synCcompl A) (synCcompl B)) (synCvv) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_difexg`. -/
@[expose]
noncomputable def gDifexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCdif A B) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCdif A B))
  have p0001 := @gComplexg B W
  have p0002 := @gInexg A (synCcompl B) V (synCvv)
  have p0003 :=
    @gSylan2 (.classMem B W) (.classMem A V) (.classMem (synCcompl B) (synCvv))
      (.classMem (synCin A (synCcompl B)) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCdif A B)
      (synCin A (synCcompl B)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_symdifexg`. -/
@[expose]
noncomputable def gSymdifexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCsymdif A B) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCsymdif A B))
  have p0001 := @gDifexg A B V W
  have p0002 := @gDifexg B A W V
  have p0003 :=
    @gAncoms (.classMem B W) (.classMem A V) (.classMem (synCdif B A) (synCvv)) p0002
  have p0004 := @gUnexg (synCdif A B) (synCdif B A) (synCvv) (synCvv)
  have p0005 :=
    @gSyl2anc (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCdif A B) (synCvv)) (.classMem (synCdif B A) (synCvv))
      (.classMem (synCun (synCdif A B) (synCdif B A)) (synCvv)) p0001 p0003 p0004
  have p0006 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCsymdif A B)
      (synCun (synCdif A B) (synCdif B A)) (synCvv) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_complex`. -/
@[expose]
noncomputable def gComplex (A : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCcompl A) (synCvv)) :=
  by
  have p0000 := @gComplexg A (synCvv)
  have p0001 := Nominal.mp hyp_boolex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_inex`. -/
@[expose]
noncomputable def gInex (A : Class) (B : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_boolex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCin A B) (synCvv)) :=
  by
  have p0000 := @gInexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCin A B) (synCvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_unex`. -/
@[expose]
noncomputable def gUnex (A : Class) (B : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_boolex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCun A B) (synCvv)) :=
  by
  have p0000 := @gUnexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCun A B) (synCvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_difex`. -/
@[expose]
noncomputable def gDifex (A : Class) (B : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_boolex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCdif A B) (synCvv)) :=
  by
  have p0000 := @gDifexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCdif A B) (synCvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_symdifex`. -/
@[expose]
noncomputable def gSymdifex (A : Class) (B : Class)
    (hyp_boolex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_boolex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCsymdif A B) (synCvv)) :=
  by
  have p0000 := @gSymdifexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCsymdif A B) (synCvv)) hyp_boolex_1 hyp_boolex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_vvex`. -/
@[expose]
noncomputable def gVvex : Nominal.NPrf (.classMem (synCvv) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @gUncompl (.cv x)
  have p0001 := @gVex x
  have p0002 := @gComplex (.cv x) p0001
  have p0003 := @gUnex (.cv x) (synCcompl (.cv x)) p0001 p0002
  have p0004 :=
    @gEqeltrri (synCun (.cv x) (synCcompl (.cv x))) (synCvv) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_0ex`. -/
@[expose]
noncomputable def gN0ex : Nominal.NPrf (.classMem (synC0) (synCvv)) :=
  by
  have p0000 := @gComplV
  have p0001 := @gVvex
  have p0002 := @gComplex (synCvv) p0001
  have p0003 := @gEqeltrri (synCcompl (synCvv)) (synC0) (synCvv) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_snex`. -/
@[expose]
noncomputable def gSnex (A : Class) : Nominal.NPrf (.classMem (synCsn A) (synCvv)) :=
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
  have p0000 := @gSneq (.cv x) A
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCsn (.cv x)) (synCsn A) (synCvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axSn x y z
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0003 :=
    @gIsset y (synCsn (.cv x))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton] at ⊢;
            aesop))
  have p0004 :=
    @gAxprimlem1 (.cv x) y z
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0005_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv y) (synCsn (.cv x)))
        (.all z (synWb (.objMem z y) (.objEq z x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
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
    @gExbii (.classEq (.cv y) (synCsn (.cv x)))
      (.all z (synWb (.objMem z y) (.objEq z x))) y p0005_e00_recanon
  have p0006 :=
    @gBitri (.classMem (synCsn (.cv x)) (synCvv))
      (synWex y (.classEq (.cv y) (synCsn (.cv x))))
      (synWex y (.all z (synWb (.objMem z y) (.objEq z x)))) p0003 p0005
  have p0007 :=
    @gMpbir (.classMem (synCsn (.cv x)) (synCvv))
      (synWex y (.all z (synWb (.objMem z y) (.objEq z x)))) p0002 p0006
  have p0008 :=
    @gVtoclg (.classMem (synCsn (.cv x)) (synCvv)) (.classMem (synCsn A) (synCvv)) x
      A (synCvv)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      p0001 p0007
  have p0009 := @gSnprc A
  have p0010 :=
    @gBiimpi (.neg (.classMem A (synCvv))) (.classEq (synCsn A) (synC0)) p0009
  have p0011 := @gN0ex
  have p0012 :=
    @gSyl6eqel (.neg (.classMem A (synCvv))) (synCsn A) (synC0) (synCvv) p0010 p0011
  have p0013 :=
    @gPm261i (.classMem A (synCvv)) (.classMem (synCsn A) (synCvv)) p0008 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_prex`. -/
@[expose]
noncomputable def gPrex (A : Class) (B : Class) :
    Nominal.NPrf (.classMem (synCpr A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCpr A B))
  have p0001 := @gSnex A
  have p0002 := @gSnex B
  have p0003 := @gUnex (synCsn A) (synCsn B) p0001 p0002
  have p0004 :=
    @gEqeltri (synCpr A B) (synCun (synCsn A) (synCsn B)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_opkex`. -/
@[expose]
noncomputable def gOpkex (A : Class) (B : Class) :
    Nominal.NPrf (.classMem (synCopk A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCopk A B))
  have p0001 := @gPrex (synCsn A) (synCpr A B)
  have p0002 :=
    @gEqeltri (synCopk A B) (synCpr (synCsn A) (synCpr A B)) (synCvv) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_snelpwg`. -/
@[expose]
noncomputable def gSnelpwg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classMem (synCsn A) (synCpw B)) (.classMem A B))) :=
  by
  have p0000 := @gSnssg A B V
  have p0001 := @gSnex A
  have p0002 := @gElpw (synCsn A) B p0001
  have p0003 :=
    @gSyl6rbbr (.classMem A V) (.classMem A B) (synWss (synCsn A) B)
      (.classMem (synCsn A) (synCpw B)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_snelpw`. -/
@[expose]
noncomputable def gSnelpw (A : Class) (B : Class)
    (hyp_snelpw_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (.classMem (synCsn A) (synCpw B)) (.classMem A B)) :=
  by
  have p0000 := @gSnelpwg A B (synCvv)
  have p0001 := Nominal.mp hyp_snelpw_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_snelpwi`. -/
@[expose]
noncomputable def gSnelpwi (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classMem (synCsn A) (synCpw B))) :=
  by
  have p0000 := @gSnssi A B
  have p0001 := @gSnex A
  have p0002 := @gElpw (synCsn A) B p0001
  have p0003 :=
    @gSylibr (.classMem A B) (synWss (synCsn A) B) (.classMem (synCsn A) (synCpw B))
      p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_unipw`. -/
@[expose]
noncomputable def gUnipw (A : Class) :
    Nominal.NPrf (.classEq (synCuni (synCpw A)) A) :=
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
    @gEluni y (.cv x) (synCpw A)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
  have p0001 := @gVex y
  have p0002 := @gElpw (.cv y) A p0001
  have p0003 := @gSsel (.cv y) A (.cv x)
  have p0004 :=
    @gSylbi (.classMem (.cv y) (synCpw A)) (synWss (.cv y) A)
      (.imp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) A)) p0002 p0003
  have p0005 :=
    @gImpcom (.classMem (.cv y) (synCpw A)) (.classMem (.cv x) (.cv y))
      (.classMem (.cv x) A) p0004
  have p0006 :=
    @gExlimiv (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (synCpw A)))
      (.classMem (.cv x) A) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0005
  have p0007 :=
    @gSylbi (.classMem (.cv x) (synCuni (synCpw A)))
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) (synCpw A))))
      (.classMem (.cv x) A) p0000 p0006
  have p0008 := @gVex x
  have p0009 := @gSnid (.cv x) p0008
  have p0010 := @gSnelpwi (.cv x) A
  have p0011 := @gElunii (.cv x) (synCsn (.cv x)) (synCpw A)
  have p0012 :=
    @gSylancr (.classMem (.cv x) A) (.classMem (.cv x) (synCsn (.cv x)))
      (.classMem (synCsn (.cv x)) (synCpw A)) (.classMem (.cv x) (synCuni (synCpw A)))
      p0009 p0010 p0011
  have p0013 :=
    @gImpbii (.classMem (.cv x) (synCuni (synCpw A))) (.classMem (.cv x) A) p0007 p0012
  have p0014 :=
    @gEqriv x (synCuni (synCpw A)) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
      (by
        aesop)
      p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_sspwb`. -/
@[expose]
noncomputable def gSspwb (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (synWss (synCpw A) (synCpw B))) :=
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
  have p0000 := @gSstr2 (.cv x) A B
  have p0001 := @gCom12 (synWss (.cv x) A) (synWss A B) (synWss (.cv x) B) p0000
  have p0002 := @gVex x
  have p0003 := @gElpw (.cv x) A p0002
  have p0004 := @gElpw (.cv x) B p0002
  have p0005 :=
    @gN3imtr4g (synWss A B) (synWss (.cv x) A) (synWss (.cv x) B)
      (.classMem (.cv x) (synCpw A)) (.classMem (.cv x) (synCpw B)) p0001 p0003 p0004
  have p0006 :=
    @gSsrdv (synWss A B) x (synCpw A) (synCpw B)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0005
  have p0007 := @gSsel (synCpw A) (synCpw B) (synCsn (.cv x))
  have p0008 := @gSnex (.cv x)
  have p0009 := @gElpw (synCsn (.cv x)) A p0008
  have p0010 := @gSnss (.cv x) A p0002
  have p0011 :=
    @gBitr4i (.classMem (synCsn (.cv x)) (synCpw A)) (synWss (synCsn (.cv x)) A)
      (.classMem (.cv x) A) p0009 p0010
  have p0012 := @gElpw (synCsn (.cv x)) B p0008
  have p0013 := @gSnss (.cv x) B p0002
  have p0014 :=
    @gBitr4i (.classMem (synCsn (.cv x)) (synCpw B)) (synWss (synCsn (.cv x)) B)
      (.classMem (.cv x) B) p0012 p0013
  have p0015 :=
    @gN3imtr3g (synWss (synCpw A) (synCpw B))
      (.classMem (synCsn (.cv x)) (synCpw A)) (.classMem (synCsn (.cv x)) (synCpw B))
      (.classMem (.cv x) A) (.classMem (.cv x) B) p0007 p0011 p0014
  have p0016 :=
    @gSsrdv (synWss (synCpw A) (synCpw B)) x A B
      (by
        aesop)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              Finset.mem_union] at ⊢;
            aesop))
      p0015
  have p0017 := @gImpbii (synWss A B) (synWss (synCpw A) (synCpw B)) p0006 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_pwadjoin`. -/
@[expose]
noncomputable def gPwadjoin (A : Class) (X : Class) (a : Var) (b : Var)
    (dv_A_a : a ∉ A.fv) (dv_A_b : b ∉ A.fv) (dv_X_a : a ∉ X.fv) (dv_X_b : b ∉ X.fv)
    (dv_a_b : a ≠ b) :
    Nominal.NPrf
      (.classEq (synCpw (synCun A (synCsn X))) (synCun (synCpw A) (.cab a
            (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))))) :=
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
  have p0000 := @gUncom A (synCsn X)
  have p0001 := @gSseq2i (synCun A (synCsn X)) (synCun (synCsn X) A) (.cv z) p0000
  have p0002 := @gSsundif (.cv z) (synCsn X) A
  have p0003 :=
    @gBitri (synWss (.cv z) (synCun A (synCsn X)))
      (synWss (.cv z) (synCun (synCsn X) A)) (synWss (synCdif (.cv z) (synCsn X)) A)
      p0001 p0002
  have p0004 :=
    @gBiimpi (synWss (.cv z) (synCun A (synCsn X)))
      (synWss (synCdif (.cv z) (synCsn X)) A) p0003
  have p0005 :=
    @gAdantr (synWss (.cv z) (synCun A (synCsn X)))
      (synWss (synCdif (.cv z) (synCsn X)) A) (.classMem X (.cv z)) p0004
  have p0006 := @gVex z
  have p0007 := @gSnex X
  have p0008 := @gDifex (.cv z) (synCsn X) p0006 p0007
  have p0009 := @gElpw (synCdif (.cv z) (synCsn X)) A p0008
  have p0010 :=
    @gSylibr (synWa (synWss (.cv z) (synCun A (synCsn X))) (.classMem X (.cv z)))
      (synWss (synCdif (.cv z) (synCsn X)) A)
      (.classMem (synCdif (.cv z) (synCsn X)) (synCpw A)) p0005 p0009
  have p0011 := @gDifsnid (.cv z) X
  have p0012 :=
    @gEqcomd (.classMem X (.cv z)) (synCun (synCdif (.cv z) (synCsn X)) (synCsn X))
      (.cv z) p0011
  have p0013 :=
    @gAdantl (.classMem X (.cv z))
      (.classEq (.cv z) (synCun (synCdif (.cv z) (synCsn X)) (synCsn X)))
      (synWss (.cv z) (synCun A (synCsn X))) p0012
  have p0014 := @gUneq1 (.cv b) (synCdif (.cv z) (synCsn X)) (synCsn X)
  have p0015 :=
    @gEqeq2d (.classEq (.cv b) (synCdif (.cv z) (synCsn X)))
      (synCun (.cv b) (synCsn X)) (synCun (synCdif (.cv z) (synCsn X)) (synCsn X))
      (.cv z) p0014
  have p0016 :=
    @gRspcev (.classEq (.cv z) (synCun (.cv b) (synCsn X)))
      (.classEq (.cv z) (synCun (synCdif (.cv z) (synCsn X)) (synCsn X))) b
      (synCdif (.cv z) (synCsn X)) (synCpw A)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw] at ⊢;
            aesop))
      (by
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
    @gSyl2anc (synWa (synWss (.cv z) (synCun A (synCsn X))) (.classMem X (.cv z)))
      (.classMem (synCdif (.cv z) (synCsn X)) (synCpw A))
      (.classEq (.cv z) (synCun (synCdif (.cv z) (synCsn X)) (synCsn X)))
      (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))) p0010
      p0013 p0016
  have p0018 :=
    @gEx (synWss (.cv z) (synCun A (synCsn X))) (.classMem X (.cv z))
      (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))) p0017
  have p0019 :=
    @gCon3d (synWss (.cv z) (synCun A (synCsn X))) (.classMem X (.cv z))
      (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))) p0018
  have p0020 := @gSsel (.cv z) (synCun A (synCsn X)) (.cv x)
  have p0021_e00_recanon :
    Nominal.NPrf
      (.imp (synWss (.cv z) (synCun A (synCsn X)))
        (.imp (.objMem x z) (.classMem (.cv x) (synCun A (synCsn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWss synCin synCcompl synCnin synWnan synWa synCun synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0021 :=
    @gCom12 (synWss (.cv z) (synCun A (synCsn X))) (.objMem x z)
      (.classMem (.cv x) (synCun A (synCsn X))) p0021_e00_recanon
  have p0022 := @gElun (.cv x) A (synCsn X)
  have p0023 :=
    @gElsn x X
      (by
        aesop)
  have p0024 :=
    @gOrbi2i (.classMem (.cv x) (synCsn X)) (.classEq (.cv x) X) (.classMem (.cv x) A)
      p0023
  have p0025 :=
    @gBitri (.classMem (.cv x) (synCun A (synCsn X)))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) (synCsn X)))
      (synWo (.classMem (.cv x) A) (.classEq (.cv x) X)) p0022 p0024
  have p0026 :=
    Nominal.ax1 (.classMem (.cv x) A) (synWa (.objMem x z) (.neg (.classMem X (.cv z))))
  have p0027 := @gEleq1 (.cv x) X (.cv z)
  have p0028_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) X) (synWb (.objMem x z) (.classMem X (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gAnbi1d (.classEq (.cv x) X) (.objMem x z) (.classMem X (.cv z))
      (.neg (.classMem X (.cv z))) p0028_e00_recanon
  have p0029 := @gPm221 (.classMem X (.cv z)) (.classMem (.cv x) A)
  have p0030 :=
    @gImpcom (.neg (.classMem X (.cv z))) (.classMem X (.cv z)) (.classMem (.cv x) A)
      p0029
  have p0031 :=
    @gSyl6bi (.classEq (.cv x) X) (synWa (.objMem x z) (.neg (.classMem X (.cv z))))
      (synWa (.classMem X (.cv z)) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A)
      p0028 p0030
  have p0032 :=
    @gJaoi (.classMem (.cv x) A)
      (.imp (synWa (.objMem x z) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A))
      (.classEq (.cv x) X) p0026 p0031
  have p0033 :=
    @gSylbi (.classMem (.cv x) (synCun A (synCsn X)))
      (synWo (.classMem (.cv x) A) (.classEq (.cv x) X))
      (.imp (synWa (.objMem x z) (.neg (.classMem X (.cv z)))) (.classMem (.cv x) A))
      p0025 p0032
  have p0034 :=
    @gExp3a (.classMem (.cv x) (synCun A (synCsn X))) (.objMem x z)
      (.neg (.classMem X (.cv z))) (.classMem (.cv x) A) p0033
  have p0035 :=
    @gCom12 (.classMem (.cv x) (synCun A (synCsn X))) (.objMem x z)
      (.imp (.neg (.classMem X (.cv z))) (.classMem (.cv x) A)) p0034
  have p0036 :=
    @gSyld (.objMem x z) (synWss (.cv z) (synCun A (synCsn X)))
      (.classMem (.cv x) (synCun A (synCsn X)))
      (.imp (.neg (.classMem X (.cv z))) (.classMem (.cv x) A)) p0021 p0035
  have p0037 :=
    @gImp3a (.objMem x z) (synWss (.cv z) (synCun A (synCsn X)))
      (.neg (.classMem X (.cv z))) (.classMem (.cv x) A) p0036
  have p0038 :=
    @gCom12 (.objMem x z)
      (synWa (synWss (.cv z) (synCun A (synCsn X))) (.neg (.classMem X (.cv z))))
      (.classMem (.cv x) A) p0037
  have p0039_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWss (.cv z) (synCun A (synCsn X))) (.neg (.classMem X (.cv z))))
        (.imp (.classMem (.cv x) (.cv z)) (.classMem (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWss synCin synCcompl synCnin synWnan synCun synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @gSsrdv
      (synWa (synWss (.cv z) (synCun A (synCsn X))) (.neg (.classMem X (.cv z)))) x
      (.cv z) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      (by
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
    @gEx (synWss (.cv z) (synCun A (synCsn X))) (.neg (.classMem X (.cv z)))
      (synWss (.cv z) A) p0039
  have p0041 :=
    @gSyld (synWss (.cv z) (synCun A (synCsn X)))
      (.neg (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))))
      (.neg (.classMem X (.cv z))) (synWss (.cv z) A) p0019 p0040
  have p0042 :=
    @gOrrd (synWss (.cv z) (synCun A (synCsn X)))
      (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X))))
      (synWss (.cv z) A) p0041
  have p0043 :=
    @gOrcomd (synWss (.cv z) (synCun A (synCsn X)))
      (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X))))
      (synWss (.cv z) A) p0042
  have p0044 := @gSsun3 (.cv z) A (synCsn X)
  have p0045 := @gVex b
  have p0046 := @gElpw (.cv b) A p0045
  have p0047 := @gUnss1 (.cv b) A (synCsn X)
  have p0048 :=
    @gSylbi (.classMem (.cv b) (synCpw A)) (synWss (.cv b) A)
      (synWss (synCun (.cv b) (synCsn X)) (synCun A (synCsn X))) p0046 p0047
  have p0049 := @gSseq1 (.cv z) (synCun (.cv b) (synCsn X)) (synCun A (synCsn X))
  have p0050 :=
    @gSyl5ibrcom (.classMem (.cv b) (synCpw A))
      (synWss (.cv z) (synCun A (synCsn X)))
      (.classEq (.cv z) (synCun (.cv b) (synCsn X)))
      (synWss (synCun (.cv b) (synCsn X)) (synCun A (synCsn X))) p0048 p0049
  have p0051 :=
    @gRexlimiv (.classEq (.cv z) (synCun (.cv b) (synCsn X)))
      (synWss (.cv z) (synCun A (synCsn X))) b (synCpw A)
      (by
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
    @gJaoi (synWss (.cv z) A) (synWss (.cv z) (synCun A (synCsn X)))
      (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))) p0044
      p0051
  have p0053 :=
    @gImpbii (synWss (.cv z) (synCun A (synCsn X)))
      (synWo (synWss (.cv z) A)
        (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))))
      p0043 p0052
  have p0054 := @gElpw (.cv z) (synCun A (synCsn X)) p0006
  have p0055 :=
    @gElun (.cv z) (synCpw A)
      (.cab a (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X)))))
  have p0056 := @gElpw (.cv z) A p0006
  have p0057 := @gEqeq1 (.cv a) (.cv z) (synCun (.cv b) (synCsn X))
  have p0058_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a z) (synWb (.classEq (.cv a) (synCun (.cv b) (synCsn X)))
          (.classEq (.cv z) (synCun (.cv b) (synCsn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCsn
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0057
  have p0058 :=
    @gRexbidv (.objEq a z) (.classEq (.cv a) (synCun (.cv b) (synCsn X)))
      (.classEq (.cv z) (synCun (.cv b) (synCsn X))) b (synCpw A)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
      p0058_e00_recanon
  have p0059_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv z))
        (synWb (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))
          (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCpw, synWss, synCin,
          synCcompl, synCnin, synWnan, synCun, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @gElab (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))
      (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))) a (.cv z)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
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
    @gOrbi12i (.classMem (.cv z) (synCpw A)) (synWss (.cv z) A)
      (.classMem (.cv z) (.cab a
          (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))))
      (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))) p0056
      p0059
  have p0061 :=
    @gBitri
      (.classMem (.cv z) (synCun (synCpw A) (.cab a
            (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X)))))))
      (synWo (.classMem (.cv z) (synCpw A)) (.classMem (.cv z) (.cab a
            (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X)))))))
      (synWo (synWss (.cv z) A)
        (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))))
      p0055 p0060
  have p0062 :=
    @gN3bitr4i (synWss (.cv z) (synCun A (synCsn X)))
      (synWo (synWss (.cv z) A)
        (synWrex b (synCpw A) (.classEq (.cv z) (synCun (.cv b) (synCsn X)))))
      (.classMem (.cv z) (synCpw (synCun A (synCsn X))))
      (.classMem (.cv z) (synCun (synCpw A) (.cab a
            (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X)))))))
      p0053 p0054 p0061
  have p0063 :=
    @gEqriv z (synCpw (synCun A (synCsn X)))
      (synCun (synCpw A) (.cab a
          (synWrex b (synCpw A) (.classEq (.cv a) (synCun (.cv b) (synCsn X))))))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      (by
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

/-- Checked nominal proof certificate identified upstream as `g_preqr1`. -/
@[expose]
noncomputable def gPreqr1 (A : Class) (B : Class) (C : Class)
    (hyp_preqr1_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_preqr1_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.imp (.classEq (synCpr A C) (synCpr B C)) (.classEq A B)) :=
  by
  have p0000 := @gPrid1 A C hyp_preqr1_1
  have p0001 := @gEleq2 (synCpr A C) (synCpr B C) A
  have p0002 :=
    @gMpbii (.classEq (synCpr A C) (synCpr B C)) (.classMem A (synCpr A C))
      (.classMem A (synCpr B C)) p0000 p0001
  have p0003 := @gElpr A B C hyp_preqr1_1
  have p0004 :=
    @gSylib (.classEq (synCpr A C) (synCpr B C)) (.classMem A (synCpr B C))
      (synWo (.classEq A B) (.classEq A C)) p0002 p0003
  have p0005 := @gPrid1 B C hyp_preqr1_2
  have p0006 := @gEleq2 (synCpr A C) (synCpr B C) B
  have p0007 :=
    @gMpbiri (.classEq (synCpr A C) (synCpr B C)) (.classMem B (synCpr A C))
      (.classMem B (synCpr B C)) p0005 p0006
  have p0008 := @gElpr B A C hyp_preqr1_2
  have p0009 :=
    @gSylib (.classEq (synCpr A C) (synCpr B C)) (.classMem B (synCpr A C))
      (synWo (.classEq B A) (.classEq B C)) p0007 p0008
  have p0010 := @gEqcom A B
  have p0011 := @gEqeq2 A C B
  have p0012 :=
    @gOplem1 (.classEq (synCpr A C) (synCpr B C)) (.classEq A B) (.classEq A C)
      (.classEq B A) (.classEq B C) p0004 p0009 p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_preqr2`. -/
@[expose]
noncomputable def gPreqr2 (A : Class) (B : Class) (C : Class)
    (hyp_preqr2_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_preqr2_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.imp (.classEq (synCpr C A) (synCpr C B)) (.classEq A B)) :=
  by
  have p0000 := @gPrcom C A
  have p0001 := @gPrcom C B
  have p0002 :=
    @gEqeq12i (synCpr C A) (synCpr A C) (synCpr C B) (synCpr B C) p0000 p0001
  have p0003 := @gPreqr1 A B C hyp_preqr2_1 hyp_preqr2_2
  have p0004 :=
    @gSylbi (.classEq (synCpr C A) (synCpr C B)) (.classEq (synCpr A C) (synCpr B C))
      (.classEq A B) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_preqr2g`. -/
@[expose]
noncomputable def gPreqr2g (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (.imp (.classEq (synCpr C A) (synCpr C B)) (.classEq A B))) :=
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
  have p0000 := @gPreq2 (.cv x) A C
  have p0001 :=
    @gEqeq1d (.classEq (.cv x) A) (synCpr C (.cv x)) (synCpr C A) (synCpr C (.cv y))
      p0000
  have p0002 := @gEqeq1 (.cv x) A (.cv y)
  have p0003_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb (.objEq x y) (.classEq A (.cv y)))) :=
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
      p0002
  have p0003 :=
    @gImbi12d (.classEq (.cv x) A) (.classEq (synCpr C (.cv x)) (synCpr C (.cv y)))
      (.classEq (synCpr C A) (synCpr C (.cv y))) (.objEq x y) (.classEq A (.cv y)) p0001
      p0003_e01_recanon
  have p0004 := @gPreq2 (.cv y) B C
  have p0005 :=
    @gEqeq2d (.classEq (.cv y) B) (synCpr C (.cv y)) (synCpr C B) (synCpr C A) p0004
  have p0006 := @gEqeq2 (.cv y) B A
  have p0007 :=
    @gImbi12d (.classEq (.cv y) B) (.classEq (synCpr C A) (synCpr C (.cv y)))
      (.classEq (synCpr C A) (synCpr C B)) (.classEq A (.cv y)) (.classEq A B) p0005
      p0006
  have p0008 := @gVex x
  have p0009 := @gVex y
  have p0010 := @gPreqr2 (.cv x) (.cv y) C p0008 p0009
  have p0011_e02_recanon :
    Nominal.NPrf (.imp (.classEq (synCpr C (.cv x)) (synCpr C (.cv y))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpr synCun synCnin synWnan synWa synCcompl synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0010
  have p0011 :=
    @gVtocl2g (.imp (.classEq (synCpr C (.cv x)) (synCpr C (.cv y))) (.objEq x y))
      (.imp (.classEq (synCpr C A) (synCpr C (.cv y))) (.classEq A (.cv y)))
      (.imp (.classEq (synCpr C A) (synCpr C B)) (.classEq A B)) x y A B V W
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0003 p0007 p0011_e02_recanon
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_elopk`. -/
@[expose]
noncomputable def gElopk (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem A (synCopk B C))
        (synWo (.classEq A (synCsn B)) (.classEq A (synCpr B C)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCopk B C))
  have p0001 := @gEleq2i (synCopk B C) (synCpr (synCsn B) (synCpr B C)) A p0000
  have p0002 := @gSnex B
  have p0003 := @gPrex B C
  have p0004 := @gElpr2 A (synCsn B) (synCpr B C) p0002 p0003
  have p0005 :=
    @gBitri (.classMem A (synCopk B C))
      (.classMem A (synCpr (synCsn B) (synCpr B C)))
      (synWo (.classEq A (synCsn B)) (.classEq A (synCpr B C))) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_opkth1g`. -/
@[expose]
noncomputable def gOpkth1g (A : Class) (B : Class) (C : Class) (D : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classEq (synCopk A B) (synCopk C D))) (.classEq A C)) :=
  by
  have p0000 := @gEqid (synCsn C)
  have p0001 :=
    @gOrci (.classEq (synCsn C) (synCsn C)) (.classEq (synCsn C) (synCpr C D)) p0000
  have p0002 := @gElopk (synCsn C) C D
  have p0003 :=
    @gMpbir (.classMem (synCsn C) (synCopk C D))
      (synWo (.classEq (synCsn C) (synCsn C)) (.classEq (synCsn C) (synCpr C D)))
      p0001 p0002
  have p0004 := @gEleq2 (synCopk A B) (synCopk C D) (synCsn C)
  have p0005 :=
    @gBiimprd (.classEq (synCopk A B) (synCopk C D))
      (.classMem (synCsn C) (synCopk A B)) (.classMem (synCsn C) (synCopk C D)) p0004
  have p0006 := @gElopk (synCsn C) A B
  have p0007 := @gSnidg A V
  have p0008 := @gEleq2 (synCsn C) (synCsn A) A
  have p0009 :=
    @gSyl5ibrcom (.classMem A V) (.classMem A (synCsn C))
      (.classEq (synCsn C) (synCsn A)) (.classMem A (synCsn A)) p0007 p0008
  have p0010 := @gPrid1g A B V
  have p0011 := @gEleq2 (synCsn C) (synCpr A B) A
  have p0012 :=
    @gSyl5ibrcom (.classMem A V) (.classMem A (synCsn C))
      (.classEq (synCsn C) (synCpr A B)) (.classMem A (synCpr A B)) p0010 p0011
  have p0013 :=
    @gJaod (.classMem A V) (.classEq (synCsn C) (synCsn A)) (.classMem A (synCsn C))
      (.classEq (synCsn C) (synCpr A B)) p0009 p0012
  have p0014 :=
    @gSyl5bi (.classMem (synCsn C) (synCopk A B))
      (synWo (.classEq (synCsn C) (synCsn A)) (.classEq (synCsn C) (synCpr A B)))
      (.classMem A V) (.classMem A (synCsn C)) p0006 p0013
  have p0015 :=
    @gSylan9r (.classEq (synCopk A B) (synCopk C D))
      (.classMem (synCsn C) (synCopk C D)) (.classMem (synCsn C) (synCopk A B))
      (.classMem A V) (.classMem A (synCsn C)) p0005 p0014
  have p0016 :=
    @gMpi (synWa (.classMem A V) (.classEq (synCopk A B) (synCopk C D)))
      (.classMem (synCsn C) (synCopk C D)) (.classMem A (synCsn C)) p0003 p0015
  have p0017 := @gElsncg A C V
  have p0018 :=
    @gAdantr (.classMem A V) (synWb (.classMem A (synCsn C)) (.classEq A C))
      (.classEq (synCopk A B) (synCopk C D)) p0017
  have p0019 :=
    @gMpbid (synWa (.classMem A V) (.classEq (synCopk A B) (synCopk C D)))
      (.classMem A (synCsn C)) (.classEq A C) p0016 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_opkthg`. -/
@[expose]
noncomputable def gOpkthg (A : Class) (B : Class) (C : Class) (D : Class) (T : Class)
    (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem D T))
        (synWb (.classEq (synCopk A B) (synCopk C D))
          (synWa (.classEq A C) (.classEq B D)))) :=
  by
  have p0000 := @gSimp1 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0001 := @gOpkth1g A B C D V
  have p0002 :=
    @gSylan (synW3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classMem A V)
      (.classEq (synCopk A B) (synCopk C D)) (.classEq A C) p0000 p0001
  have p0003 := @gSimp2 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0004 := @gSimp3 (.classMem A V) (.classMem B W) (.classMem D T)
  have p0005 :=
    @gJca (synW3a (.classMem A V) (.classMem B W) (.classMem D T)) (.classMem B W)
      (.classMem D T) p0003 p0004
  have p0006 := @gOpkeq1 A C B
  have p0007 :=
    @gEqeq1d (.classEq A C) (synCopk A B) (synCopk C B) (synCopk C D) p0006
  have p0008 :=
    @gBiimpd (.classEq A C) (.classEq (synCopk A B) (synCopk C D))
      (.classEq (synCopk C B) (synCopk C D)) p0007
  have p0009 :=
    @gImpcom (.classEq A C) (.classEq (synCopk A B) (synCopk C D))
      (.classEq (synCopk C B) (synCopk C D)) p0008
  have p0010 := (Nominal.classEqRefl (synCopk C B))
  have p0011 := (Nominal.classEqRefl (synCopk C D))
  have p0012 :=
    @gEqeq12i (synCopk C B) (synCpr (synCsn C) (synCpr C B)) (synCopk C D)
      (synCpr (synCsn C) (synCpr C D)) p0010 p0011
  have p0013 := @gPrex C B
  have p0014 := @gPrex C D
  have p0015 := @gPreqr2 (synCpr C B) (synCpr C D) (synCsn C) p0013 p0014
  have p0016 :=
    @gSylbi (.classEq (synCopk C B) (synCopk C D))
      (.classEq (synCpr (synCsn C) (synCpr C B)) (synCpr (synCsn C) (synCpr C D)))
      (.classEq (synCpr C B) (synCpr C D)) p0012 p0015
  have p0017 := @gPreqr2g B D C W T
  have p0018 :=
    @gSyl5 (.classEq (synCopk C B) (synCopk C D))
      (.classEq (synCpr C B) (synCpr C D)) (synWa (.classMem B W) (.classMem D T))
      (.classEq B D) p0016 p0017
  have p0019 :=
    @gSyl5 (synWa (.classEq (synCopk A B) (synCopk C D)) (.classEq A C))
      (.classEq (synCopk C B) (synCopk C D)) (synWa (.classMem B W) (.classMem D T))
      (.classEq B D) p0009 p0018
  have p0020 :=
    @gExp3a (synWa (.classMem B W) (.classMem D T))
      (.classEq (synCopk A B) (synCopk C D)) (.classEq A C) (.classEq B D) p0019
  have p0021 :=
    @gImp (synWa (.classMem B W) (.classMem D T))
      (.classEq (synCopk A B) (synCopk C D)) (.imp (.classEq A C) (.classEq B D)) p0020
  have p0022 :=
    @gSylan (synW3a (.classMem A V) (.classMem B W) (.classMem D T))
      (synWa (.classMem B W) (.classMem D T)) (.classEq (synCopk A B) (synCopk C D))
      (.imp (.classEq A C) (.classEq B D)) p0005 p0021
  have p0023 :=
    @gJcai
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classMem D T))
        (.classEq (synCopk A B) (synCopk C D)))
      (.classEq A C) (.classEq B D) p0002 p0022
  have p0024 :=
    @gEx (synW3a (.classMem A V) (.classMem B W) (.classMem D T))
      (.classEq (synCopk A B) (synCopk C D)) (synWa (.classEq A C) (.classEq B D))
      p0023
  have p0025 := @gOpkeq12 A B C D
  have p0026 :=
    @gImpbid1 (synW3a (.classMem A V) (.classMem B W) (.classMem D T))
      (.classEq (synCopk A B) (synCopk C D)) (synWa (.classEq A C) (.classEq B D))
      p0024 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_el1c`. -/
@[expose]
noncomputable def gEl1c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synC1c)) (synWex x (.classEq A (synCsn (.cv x))))) :=
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
  have p0000 := @gElex A (synC1c)
  have p0001 := @gSnex (.cv x)
  have p0002 := @gEleq1 A (synCsn (.cv x)) (synCvv)
  have p0003 :=
    @gMpbiri (.classEq A (synCsn (.cv x))) (.classMem A (synCvv))
      (.classMem (synCsn (.cv x)) (synCvv)) p0001 p0002
  have p0004 :=
    @gExlimiv (.classEq A (synCsn (.cv x))) (.classMem A (synCvv)) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      p0003
  have p0005 := @gEqeq1 (.cv y) A (synCsn (.cv x))
  have p0006 :=
    @gExbidv (.classEq (.cv y) A) (.classEq (.cv y) (synCsn (.cv x)))
      (.classEq A (synCsn (.cv x))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDf1c y x
      (by
        aesop)
  have p0008 :=
    @gElab2g (synWex x (.classEq (.cv y) (synCsn (.cv x))))
      (synWex x (.classEq A (synCsn (.cv x)))) y A (synC1c) (synCvv)
      (by
        aesop)
      (by
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
    @gPm521nii (.classMem A (synC1c)) (.classMem A (synCvv))
      (synWex x (.classEq A (synCsn (.cv x)))) p0000 p0004 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_snel1c`. -/
@[expose]
noncomputable def gSnel1c (A : Class)
    (hyp_snel1c_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCsn A) (synC1c)) :=
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
  have p0000 := @gEqid (synCsn A)
  have p0001 := @gSneq (.cv x) A
  have p0002 :=
    @gEqeq2d (.classEq (.cv x) A) (synCsn (.cv x)) (synCsn A) (synCsn A) p0001
  have p0003 :=
    @gSpcev (.classEq (synCsn A) (synCsn (.cv x))) (.classEq (synCsn A) (synCsn A)) x
      A
      (by
        aesop)
      (by
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
    @gEl1c x (synCsn A)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
  have p0006 :=
    @gMpbir (.classMem (synCsn A) (synC1c))
      (synWex x (.classEq (synCsn A) (synCsn (.cv x)))) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_snel1cg`. -/
@[expose]
noncomputable def gSnel1cg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCsn A) (synC1c))) :=
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
  have p0000 := @gSneq (.cv x) A
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCsn (.cv x)) (synCsn A) (synC1c) p0000
  have p0002 := @gVex x
  have p0003 := @gSnel1c (.cv x) p0002
  have p0004 :=
    @gVtoclg (.classMem (synCsn (.cv x)) (synC1c)) (.classMem (synCsn A) (synC1c)) x
      A V
      (by
        aesop)
      (by
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

/-- Checked nominal proof certificate identified upstream as `g_n_1cex`. -/
@[expose]
noncomputable def gN1cex : Nominal.NPrf (.classMem (synC1c) (synCvv)) :=
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
  have p0001 :=
    @gIsset x (synC1c)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDf1c y z
      (by
        aesop)
  have p0003 :=
    @gEqeq2i (synC1c) (.cab y (synWex z (.classEq (.cv y) (synCsn (.cv z))))) (.cv x)
      p0002
  have p0004 :=
    @gEqabb (synWex z (.classEq (.cv y) (synCsn (.cv z)))) y (.cv x)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv x) (.cab y (synWex z (.classEq (.cv y) (synCsn (.cv z))))))
        (.all y (synWb (.objMem y x) (synWex z (.classEq (.cv y) (synCsn (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synCsn
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
    @gBitri (.classEq (.cv x) (synC1c))
      (.classEq (.cv x) (.cab y (synWex z (.classEq (.cv y) (synCsn (.cv z))))))
      (.all y (synWb (.objMem y x) (synWex z (.classEq (.cv y) (synCsn (.cv z))))))
      p0003 p0005_e01_recanon
  have p0006 :=
    @gDfcleq w (.cv y) (synCsn (.cv z))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton] at ⊢;
            aesop))
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn w (.cv z)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0008_e00_recanon :
    Nominal.NPrf (.classEq (synCsn (.cv z)) (.cab w (.objEq w z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0007
  have p0008 := @gEqabri (.objEq w z) w (synCsn (.cv z)) p0008_e00_recanon
  have p0009 :=
    @gBibi2i (.classMem (.cv w) (synCsn (.cv z))) (.objEq w z) (.objMem w y) p0008
  have p0010 :=
    @gAlbii (synWb (.objMem w y) (.classMem (.cv w) (synCsn (.cv z))))
      (synWb (.objMem w y) (.objEq w z)) w p0009
  have p0011_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv y) (synCsn (.cv z)))
        (.all w (synWb (.objMem w y) (.classMem (.cv w) (synCsn (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
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
    @gBitri (.classEq (.cv y) (synCsn (.cv z)))
      (.all w (synWb (.objMem w y) (.classMem (.cv w) (synCsn (.cv z)))))
      (.all w (synWb (.objMem w y) (.objEq w z))) p0011_e00_recanon p0010
  have p0012 :=
    @gExbii (.classEq (.cv y) (synCsn (.cv z)))
      (.all w (synWb (.objMem w y) (.objEq w z))) z p0011
  have p0013 :=
    @gBibi2i (synWex z (.classEq (.cv y) (synCsn (.cv z))))
      (synWex z (.all w (synWb (.objMem w y) (.objEq w z)))) (.objMem y x) p0012
  have p0014 :=
    @gAlbii (synWb (.objMem y x) (synWex z (.classEq (.cv y) (synCsn (.cv z)))))
      (synWb (.objMem y x) (synWex z (.all w (synWb (.objMem w y) (.objEq w z))))) y
      p0013
  have p0015 :=
    @gBitri (.classEq (.cv x) (synC1c))
      (.all y (synWb (.objMem y x) (synWex z (.classEq (.cv y) (synCsn (.cv z))))))
      (.all y (synWb (.objMem y x) (synWex z (.all w (synWb (.objMem w y) (.objEq w z))))))
      p0005 p0014
  have p0016 :=
    @gExbii (.classEq (.cv x) (synC1c))
      (.all y (synWb (.objMem y x) (synWex z (.all w (synWb (.objMem w y) (.objEq w z))))))
      x p0015
  have p0017 :=
    @gBitri (.classMem (synC1c) (synCvv)) (synWex x (.classEq (.cv x) (synC1c)))
      (synWex x (.all y (synWb (.objMem y x)
            (synWex z (.all w (synWb (.objMem w y) (.objEq w z)))))))
      p0001 p0016
  have p0018 :=
    @gMpbir (.classMem (synC1c) (synCvv))
      (synWex x (.all y (synWb (.objMem y x)
            (synWex z (.all w (synWb (.objMem w y) (.objEq w z)))))))
      p0000 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_pw1eq`. -/
@[expose]
noncomputable def gPw1eq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCpw1 A) (synCpw1 B))) :=
  by
  have p0000 := @gPweq A B
  have p0001 := @gIneq1d (.classEq A B) (synCpw A) (synCpw B) (synC1c) p0000
  have p0002 := (Nominal.classEqRefl (synCpw1 A))
  have p0003 := (Nominal.classEqRefl (synCpw1 B))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCin (synCpw A) (synC1c))
      (synCin (synCpw B) (synC1c)) (synCpw1 A) (synCpw1 B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_elpw1`. -/
@[expose]
noncomputable def gElpw1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 B)) (synWrex x B (.classEq A (synCsn (.cv x))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCpw1 B))
  have p0001 := @gEleq2i (synCpw1 B) (synCin (synCpw B) (synC1c)) A p0000
  have p0002 := @gElin A (synCpw B) (synC1c)
  have p0003 :=
    @gBitri (.classMem A (synCpw1 B)) (.classMem A (synCin (synCpw B) (synC1c)))
      (synWa (.classMem A (synCpw B)) (.classMem A (synC1c))) p0001 p0002
  have p0004 :=
    @gEl1c x A
      (by
        aesop)
  have p0005 :=
    @gAnbi2i (.classMem A (synC1c)) (synWex x (.classEq A (synCsn (.cv x))))
      (.classMem A (synCpw B)) p0004
  have p0006 :=
    @gN1942v (.classMem A (synCpw B)) (.classEq A (synCsn (.cv x))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              Finset.mem_union] at ⊢;
            aesop))
  have p0007 :=
    @gBitr4i (synWa (.classMem A (synCpw B)) (.classMem A (synC1c)))
      (synWa (.classMem A (synCpw B)) (synWex x (.classEq A (synCsn (.cv x)))))
      (synWex x (synWa (.classMem A (synCpw B)) (.classEq A (synCsn (.cv x))))) p0005
      p0006
  have p0008 := @gEleq1 A (synCsn (.cv x)) (synCpw B)
  have p0009 := @gSnex (.cv x)
  have p0010 := @gElpw (synCsn (.cv x)) B p0009
  have p0011 := @gVex x
  have p0012 := @gSnss (.cv x) B p0011
  have p0013 :=
    @gBitr4i (.classMem (synCsn (.cv x)) (synCpw B)) (synWss (synCsn (.cv x)) B)
      (.classMem (.cv x) B) p0010 p0012
  have p0014 :=
    @gSyl6bb (.classEq A (synCsn (.cv x))) (.classMem A (synCpw B))
      (.classMem (synCsn (.cv x)) (synCpw B)) (.classMem (.cv x) B) p0008 p0013
  have p0015 :=
    @gPm532ri (.classEq A (synCsn (.cv x))) (.classMem A (synCpw B))
      (.classMem (.cv x) B) p0014
  have p0016 :=
    @gExbii (synWa (.classMem A (synCpw B)) (.classEq A (synCsn (.cv x))))
      (synWa (.classMem (.cv x) B) (.classEq A (synCsn (.cv x)))) x p0015
  have p0017 := (Nominal.biimpRefl (synWrex x B (.classEq A (synCsn (.cv x)))))
  have p0018 :=
    @gBitr4i
      (synWex x (synWa (.classMem A (synCpw B)) (.classEq A (synCsn (.cv x)))))
      (synWex x (synWa (.classMem (.cv x) B) (.classEq A (synCsn (.cv x)))))
      (synWrex x B (.classEq A (synCsn (.cv x)))) p0016 p0017
  have p0019 :=
    @gBitri (synWa (.classMem A (synCpw B)) (.classMem A (synC1c)))
      (synWex x (synWa (.classMem A (synCpw B)) (.classEq A (synCsn (.cv x)))))
      (synWrex x B (.classEq A (synCsn (.cv x)))) p0007 p0018
  have p0020 :=
    @gBitri (.classMem A (synCpw1 B))
      (synWa (.classMem A (synCpw B)) (.classMem A (synC1c)))
      (synWrex x B (.classEq A (synCsn (.cv x)))) p0003 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_elpw12`. -/
@[expose]
noncomputable def gElpw12 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 B)))
        (synWrex x B (.classEq A (synCsn (synCsn (.cv x)))))) :=
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
    @gElpw1 y A (synCpw1 B)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1] at ⊢;
            aesop))
  have p0001 :=
    @gElpw1 x (.cv y) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
  have p0002 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 B))
      (synWrex x B (.classEq (.cv y) (synCsn (.cv x)))) (.classEq A (synCsn (.cv y)))
      p0001
  have p0003 :=
    @gR1941v (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))) x B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0004 :=
    @gBitr4i (synWa (.classMem (.cv y) (synCpw1 B)) (.classEq A (synCsn (.cv y))))
      (synWa (synWrex x B (.classEq (.cv y) (synCsn (.cv x))))
        (.classEq A (synCsn (.cv y))))
      (synWrex x B
        (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y)))))
      p0002 p0003
  have p0005 :=
    @gExbii (synWa (.classMem (.cv y) (synCpw1 B)) (.classEq A (synCsn (.cv y))))
      (synWrex x B
        (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y)))))
      y p0004
  have p0006 :=
    (Nominal.biimpRefl (synWrex y (synCpw1 B) (.classEq A (synCsn (.cv y)))))
  have p0007 :=
    @gRexcom4
      (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y)))) x y B
      (by
        aesop)
      (by
        aesop)
  have p0008 :=
    @gN3bitr4i
      (synWex y (synWa (.classMem (.cv y) (synCpw1 B)) (.classEq A (synCsn (.cv y)))))
      (synWex y (synWrex x B
          (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))))))
      (synWrex y (synCpw1 B) (.classEq A (synCsn (.cv y))))
      (synWrex x B (synWex y
          (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))))))
      p0005 p0006 p0007
  have p0009 := @gSnex (.cv x)
  have p0010 := @gSneq (.cv y) (synCsn (.cv x))
  have p0011 :=
    @gEqeq2d (.classEq (.cv y) (synCsn (.cv x))) (synCsn (.cv y))
      (synCsn (synCsn (.cv x))) A p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y))) (.classEq A (synCsn (synCsn (.cv x)))) y
      (synCsn (.cv x))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton] at ⊢;
            aesop))
      (by
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
    @gRexbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (.cv x)))) x B p0012
  have p0014 :=
    @gN3bitri (.classMem A (synCpw1 (synCpw1 B)))
      (synWrex y (synCpw1 B) (.classEq A (synCsn (.cv y))))
      (synWrex x B (synWex y
          (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))))))
      (synWrex x B (.classEq A (synCsn (synCsn (.cv x))))) p0000 p0008 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay
