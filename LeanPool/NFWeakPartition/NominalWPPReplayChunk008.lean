/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SetOperations3


/-! NF weak partition development: NominalWPPReplayChunk008. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_snelpw1`. -/
@[expose]
noncomputable def gSnelpw1 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.classMem (synCsn A) (synCpw1 B)) (.classMem A B)) :=
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
  have p0000 := @gEqcom (synCsn A) (synCsn (.cv x))
  have p0001 := @gVex x
  have p0002 := @gSneqb (.cv x) A p0001
  have p0003 :=
    @gBitri (.classEq (synCsn A) (synCsn (.cv x)))
      (.classEq (synCsn (.cv x)) (synCsn A)) (.classEq (.cv x) A) p0000 p0002
  have p0004 :=
    @gRexbii (.classEq (synCsn A) (synCsn (.cv x))) (.classEq (.cv x) A) x B p0003
  have p0005 :=
    @gElpw1 x (synCsn A) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
      (by
        aesop)
  have p0006 :=
    @gRisset x A B
      (by
        aesop)
      (by
        aesop)
  have p0007 :=
    @gN3bitr4i (synWrex x B (.classEq (synCsn A) (synCsn (.cv x))))
      (synWrex x B (.classEq (.cv x) A)) (.classMem (synCsn A) (synCpw1 B))
      (.classMem A B) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_elpw11c`. -/
@[expose]
noncomputable def gElpw11c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synC1c)))
        (synWex x (.classEq A (synCsn (synCsn (.cv x)))))) :=
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
    @gElpw1 y A (synC1c)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 := (Nominal.biimpRefl (synWrex y (synC1c) (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gEl1c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i (.classMem (.cv y) (synC1c))
      (synWex x (.classEq (.cv y) (synCsn (.cv x)))) (.classEq A (synCsn (.cv y)))
      p0002
  have p0004 :=
    @gN1941v (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i (synWa (.classMem (.cv y) (synC1c)) (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (.cv x)))) (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii (synWa (.classMem (.cv y) (synC1c)) (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri (synWrex y (synC1c) (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y) (synC1c)) (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x
          (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))))
      y x
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
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (.cv x)))) x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x
          (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y
          (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (.cv x))))) p0008 p0013
  have p0015 :=
    @gN3bitri (.classMem A (synCpw1 (synC1c)))
      (synWrex y (synC1c) (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x
          (synWa (.classEq (.cv y) (synCsn (.cv x))) (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (.cv x))))) p0000 p0007 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_elpw121c`. -/
@[expose]
noncomputable def gElpw121c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 (synC1c))))
        (synWex x (.classEq A (synCsn (synCsn (synCsn (.cv x))))))) :=
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
    @gElpw1 y A (synCpw1 (synC1c))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (synWrex y (synCpw1 (synC1c)) (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gElpw11c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 (synC1c)))
      (synWex x (.classEq (.cv y) (synCsn (synCsn (.cv x)))))
      (.classEq A (synCsn (.cv y))) p0002
  have p0004 :=
    @gN1941v (.classEq (.cv y) (synCsn (synCsn (.cv x))))
      (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synC1c))) (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (synCsn (.cv x)))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synC1c))) (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri (synWrex y (synCpw1 (synC1c)) (.classEq A (synCsn (.cv y))))
      (synWex y
        (synWa (.classMem (.cv y) (synCpw1 (synC1c))) (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (.classEq A (synCsn (.cv y))))
      y x
  have p0009 := @gSnex (synCsn (.cv x))
  have p0010 := @gSneq (.cv y) (synCsn (synCsn (.cv x)))
  have p0011 :=
    @gEqeq2d (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synCsn (.cv y))
      (synCsn (synCsn (synCsn (.cv x)))) A p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn (.cv x))))) y (synCsn (synCsn (.cv x)))
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
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn (.cv x))))) x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (.cv x)))))) p0008 p0013
  have p0015 :=
    @gBitri (synWrex y (synCpw1 (synC1c)) (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (.cv x)))))) p0007 p0014
  have p0016 :=
    @gBitri (.classMem A (synCpw1 (synCpw1 (synC1c))))
      (synWrex y (synCpw1 (synC1c)) (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (.cv x)))))) p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elpw131c`. -/
@[expose]
noncomputable def gElpw131c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (.cv x)))))))) :=
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
    @gElpw1 y A (synCpw1 (synCpw1 (synC1c)))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl
      (synWrex y (synCpw1 (synCpw1 (synC1c))) (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gElpw121c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x))))))
      (.classEq A (synCsn (.cv y))) p0002
  have p0004 :=
    @gN1941v (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
      (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri (synWrex y (synCpw1 (synCpw1 (synC1c))) (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 := @gSnex (synCsn (synCsn (.cv x)))
  have p0010 := @gSneq (.cv y) (synCsn (synCsn (synCsn (.cv x))))
  have p0011 :=
    @gEqeq2d (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x))))) (synCsn (.cv y))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) A p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (.cv x)))))) y
      (synCsn (synCsn (synCsn (.cv x))))
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
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (.cv x)))))) x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (.cv x))))))) p0008 p0013
  have p0015 :=
    @gBitri (synWrex y (synCpw1 (synCpw1 (synC1c))) (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (.cv x))))))) p0007 p0014
  have p0016 :=
    @gBitri (.classMem A (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWrex y (synCpw1 (synCpw1 (synC1c))) (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (.cv x))))))) p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elpw141c`. -/
@[expose]
noncomputable def gElpw141c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synWex x
          (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))) :=
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
    @gElpw1 y A (synCpw1 (synCpw1 (synCpw1 (synC1c))))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (synWrex y (synCpw1 (synCpw1 (synCpw1 (synC1c))))
        (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gElpw131c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (.classEq A (synCsn (.cv y))) p0002
  have p0004 :=
    @gN1941v (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x
          (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 := @gSnex (synCsn (synCsn (synCsn (.cv x))))
  have p0010 := @gSneq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x)))))
  have p0011 :=
    @gEqeq2d (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCsn (.cv y)) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))) A p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))) y
      (synCsn (synCsn (synCsn (synCsn (.cv x)))))
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
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))) x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x
          (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y
          (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
      p0008 p0013
  have p0015 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x
          (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
      p0007 p0014
  have p0016 :=
    @gBitri (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elpw151c`. -/
@[expose]
noncomputable def gElpw151c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synWex x (.classEq A
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))) :=
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
    @gElpw1 y A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gElpw141c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
      (.classEq A (synCsn (.cv y))) p0002
  have p0004 :=
    @gN1941v
      (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x
          (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa
          (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa
          (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classEq A (synCsn (.cv y))))
      (synWex y
        (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa
            (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv x)))))
  have p0010 := @gSneq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
  have p0011 :=
    @gEqeq2d (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (.cv y))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))) A p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))) y
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
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
    @gExbii
      (synWex y (synWa
          (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))) x
      p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa
            (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa
            (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x
        (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      p0008 p0013
  have p0015 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa
            (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x
        (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      p0007 p0014
  have p0016 :=
    @gBitri
      (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classEq A (synCsn (.cv y))))
      (synWex x
        (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elpw161c`. -/
@[expose]
noncomputable def gElpw161c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synWex x (.classEq A (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))) :=
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
    @gElpw1 y A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gElpw151c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i
      (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWex x (.classEq (.cv y)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      (.classEq A (synCsn (.cv y))) p0002
  have p0004 :=
    @gN1941v
      (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
      (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y)
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y)
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y)
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa (.classEq (.cv y)
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 := @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
  have p0010 :=
    @gSneq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
  have p0011 :=
    @gEqeq2d
      (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
      (synCsn (.cv y))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))) A
      p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      y (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
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
    @gExbii
      (synWex y (synWa (.classEq (.cv y)
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa (.classEq (.cv y)
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y)
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      p0008 p0013
  have p0015 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa (.classEq (.cv y)
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      p0007 p0014
  have p0016 :=
    @gBitri
      (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elpw171c`. -/
@[expose]
noncomputable def gElpw171c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synWex x (.classEq A (synCsn (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))) :=
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
    @gElpw1 y A
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (synWrex y
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gElpw161c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i
      (.classMem (.cv y)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (.classEq (.cv y)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      (.classEq A (synCsn (.cv y))) p0002
  have p0004 :=
    @gN1941v
      (.classEq (.cv y)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y)
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y)
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y)
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y)
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 :=
    @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
  have p0010 :=
    @gSneq (.cv y)
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
  have p0011 :=
    @gEqeq2d
      (.classEq (.cv y)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      (synCsn (.cv y))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
      A p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      y (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
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
    @gExbii
      (synWex y (synWa (.classEq (.cv y)
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      p0008 p0013
  have p0015 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      p0007 p0014
  have p0016 :=
    @gBitri
      (.classMem A (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elpw181c`. -/
@[expose]
noncomputable def gElpw181c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) (synWex x
          (.classEq A (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))) :=
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
    @gElpw1 y A
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (synWrex y (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gElpw171c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i
      (.classMem (.cv y) (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex x (.classEq (.cv y) (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      (.classEq A (synCsn (.cv y))) p0002
  have p0004 :=
    @gN1941v
      (.classEq (.cv y) (synCsn
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri
      (synWrex y (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 :=
    @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
  have p0010 :=
    @gSneq (.cv y)
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
  have p0011 :=
    @gEqeq2d
      (.classEq (.cv y) (synCsn
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      (synCsn (.cv y))
      (synCsn (synCsn
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
      A p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      y
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
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
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      p0008 p0013
  have p0015 :=
    @gBitri
      (synWrex y (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      p0007 p0014
  have p0016 :=
    @gBitri
      (.classMem A (synCpw1 (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synWrex y (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elpw191c`. -/
@[expose]
noncomputable def gElpw191c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))) :=
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
    @gElpw1 y A
      (synCpw1 (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (synWrex y (synCpw1 (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (.classEq A (synCsn (.cv y)))))
  have p0002 :=
    @gElpw181c x (.cv y)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @gAnbi1i
      (.classMem (.cv y) (synCpw1 (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      (.classEq A (synCsn (.cv y))) p0002
  have p0004 :=
    @gN1941v
      (.classEq (.cv y) (synCsn (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      (.classEq A (synCsn (.cv y))) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 :=
    @gSnex
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
  have p0010 :=
    @gSneq (.cv y)
      (synCsn (synCsn
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
  have p0011 :=
    @gEqeq2d
      (.classEq (.cv y) (synCsn (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      (synCsn (.cv y))
      (synCsn (synCsn (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      A p0010
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      y
      (synCsn (synCsn
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
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
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      p0008 p0013
  have p0015 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      p0007 p0014
  have p0016 :=
    @gBitri
      (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWrex y (synCpw1 (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      p0000 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay
