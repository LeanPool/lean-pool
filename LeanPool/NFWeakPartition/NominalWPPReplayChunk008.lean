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

@[expose]
noncomputable def g_snelpw1 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classMem (syn_csn A) (syn_cpw1 B)) (.classMem A B)) :=
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
  have p0000 := @g_eqcom (syn_csn A) (syn_csn (.cv x))
  have p0001 := @g_vex x
  have p0002 := @g_sneqb (.cv x) A p0001
  have p0003 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv x)))
      (.classEq (syn_csn (.cv x)) (syn_csn A)) (.classEq (.cv x) A) p0000 p0002
  have p0004 :=
    @g_rexbii (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (.cv x) A) x B p0003
  have p0005 :=
    @g_elpw1 x (syn_csn A) B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    @g_risset x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0007 :=
    @g_n_3bitr4i (syn_wrex x B (.classEq (syn_csn A) (syn_csn (.cv x))))
      (syn_wrex x B (.classEq (.cv x) A)) (.classMem (syn_csn A) (syn_cpw1 B))
      (.classMem A B) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_elpw11c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_c1c)))
        (syn_wex x (.classEq A (syn_csn (syn_csn (.cv x)))))) :=
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
    @g_elpw1 y A (syn_c1c)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 := (Nominal.biimpRefl (syn_wrex y (syn_c1c) (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_el1c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_c1c))
      (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y)))
      p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_c1c)) (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_c1c)) (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_c1c) (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_c1c)) (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x
          (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))
      y x
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
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (.cv x)))) x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x
          (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (.cv x))))) p0008 p0013
  have p0015 :=
    @g_n_3bitri (.classMem A (syn_cpw1 (syn_c1c)))
      (syn_wrex y (syn_c1c) (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x
          (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (.cv x))))) p0000 p0007 p0014
  exact p0015

@[expose]
noncomputable def g_elpw121c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (.cv x))))))) :=
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
    @g_elpw1 y A (syn_cpw1 (syn_c1c))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_c1c)) (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_elpw11c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_c1c)))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))))
      (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
      (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_c1c)) (.classEq A (syn_csn (.cv y))))
      (syn_wex y
        (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 := @g_snex (syn_csn (.cv x))
  have p0010 := @g_sneq (.cv y) (syn_csn (syn_csn (.cv x)))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv y))
      (syn_csn (syn_csn (syn_csn (.cv x)))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn (.cv x))))) y (syn_csn (syn_csn (.cv x)))
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
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn (.cv x))))) x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (.cv x)))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_c1c)) (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (.cv x)))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wrex y (syn_cpw1 (syn_c1c)) (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (.cv x)))))) p0000 p0015
  exact p0016

@[expose]
noncomputable def g_elpw131c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) :=
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
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_c1c)))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_elpw121c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0010 := @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_csn (.cv y))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) y
      (syn_csn (syn_csn (syn_csn (.cv x))))
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
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) p0000 p0015
  exact p0016

@[expose]
noncomputable def g_elpw141c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wex x
          (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))) :=
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
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_elpw131c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x
          (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 := @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0010 := @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) y
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
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
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x
          (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
      p0008 p0013
  have p0015 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x
          (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
      p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_elpw151c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_wex x (.classEq A
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))) :=
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
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_elpw141c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x
          (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa
          (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa
          (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y
        (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa
            (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
  have p0010 := @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (.cv y))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) y
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
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
    @g_exbii
      (syn_wex y (syn_wa
          (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) x
      p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa
            (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa
            (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x
        (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      p0008 p0013
  have p0015 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa
            (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x
        (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      p0007 p0014
  have p0016 :=
    @g_bitri
      (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x
        (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_elpw161c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_wex x (.classEq A (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) :=
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
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_elpw151c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i
      (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wex x (.classEq (.cv y)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
      (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y)
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y)
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y)
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y)
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
  have p0011 :=
    @g_eqeq2d
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
      (syn_csn (.cv y))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))) A
      p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
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
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y)
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y)
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y)
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      p0008 p0013
  have p0015 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y)
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      p0007 p0014
  have p0016 :=
    @g_bitri
      (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_elpw171c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) :=
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
    @g_elpw1 y A
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex y
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_elpw161c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i
      (.classMem (.cv y)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex x (.classEq (.cv y)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v
      (.classEq (.cv y)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y)
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y)
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y)
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y)
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
  have p0010 :=
    @g_sneq (.cv y)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
  have p0011 :=
    @g_eqeq2d
      (.classEq (.cv y)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      (syn_csn (.cv y))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
      A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
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
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y)
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      p0008 p0013
  have p0015 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      p0007 p0014
  have p0016 :=
    @g_bitri
      (.classMem A (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_elpw181c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_wex x
          (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) :=
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
    @g_elpw1 y A
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_elpw171c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i
      (.classMem (.cv y) (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v
      (.classEq (.cv y) (syn_csn
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri
      (syn_wrex y (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
  have p0010 :=
    @g_sneq (.cv y)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
  have p0011 :=
    @g_eqeq2d
      (.classEq (.cv y) (syn_csn
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      (syn_csn (.cv y))
      (syn_csn (syn_csn
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
      A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      y
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
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
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      p0008 p0013
  have p0015 :=
    @g_bitri
      (syn_wrex y (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      p0007 p0014
  have p0016 :=
    @g_bitri
      (.classMem A (syn_cpw1 (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wrex y (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_elpw191c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) :=
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
    @g_elpw1 y A
      (syn_cpw1 (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c] at ⊢;
            aesop))
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (.classEq A (syn_csn (.cv y)))))
  have p0002 :=
    @g_elpw181c x (.cv y)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 :=
    @g_anbi1i
      (.classMem (.cv y) (syn_cpw1 (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      (.classEq A (syn_csn (.cv y))) x
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
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 :=
    @g_snex
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
  have p0010 :=
    @g_sneq (.cv y)
      (syn_csn (syn_csn
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
  have p0011 :=
    @g_eqeq2d
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      (syn_csn (.cv y))
      (syn_csn (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      y
      (syn_csn (syn_csn
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
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
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      p0008 p0013
  have p0015 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      p0007 p0014
  have p0016 :=
    @g_bitri
      (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      p0000 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay
