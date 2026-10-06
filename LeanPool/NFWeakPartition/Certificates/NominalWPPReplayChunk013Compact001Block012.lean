/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part055`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_taddc`. -/
@[expose]
noncomputable def gTaddc (A : Class) (B : Class) (X : Class) (c : Var)
    (dv_X_c : c ∉ X.fv) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
            (.classMem X (synCncs))) (.classEq (synCtc A) (synCplc (synCtc B) X)))
        (synWrex c (synCncs) (.classEq X (synCtc (.cv c))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ X.fv ∪ ({ c } : Finset Var)
  let w : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_X : w ∉ X.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_ne_c : w ≠ c := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_w : c ≠ w := Ne.symm fresh_w_ne_c
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_c : x ≠ c := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
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
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
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
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_c : z ≠ c := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_z : c ≠ z := Ne.symm fresh_z_ne_c
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_ne_c : a ≠ c := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_b_ne_c : b ≠ c := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_w_ne_x : w ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_ne_a : w ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_w : a ≠ w := Ne.symm fresh_w_ne_a
  have fresh_w_ne_b : w ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_b_ne_w : b ≠ w := Ne.symm fresh_w_ne_b
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : z ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_X, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq X (synCnc (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_z, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.classEq X (synCnc (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_X, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq A (synCnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Wff.classEq A (synCnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq B (synCnc (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Wff.classEq B (synCnc (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_B, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : a ∉ ((synCpw1 (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_x,
          not_false_eq_true])
  have dv_cache_0013 : b ∉ ((synCpw1 (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_x,
          not_false_eq_true])
  have dv_cache_0014 : a ∉ ((synCnc (synCpw1 (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_y,
          not_false_eq_true])
  have dv_cache_0015 : b ∉ ((synCnc (synCpw1 (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_y,
          not_false_eq_true])
  have dv_cache_0016 : a ∉ ((synCnc (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_z,
          not_false_eq_true])
  have dv_cache_0017 : b ∉ ((synCnc (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_z,
          not_false_eq_true])
  have dv_cache_0018 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0019 : c ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_a, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_a, not_false_eq_true])
  have dv_cache_0021 : c ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_b, not_false_eq_true])
  have dv_cache_0022 : w ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_b, not_false_eq_true])
  have dv_cache_0023 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0024 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0025 : c ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show c ≠ w from (by exact fresh_c_ne_w))
  have dv_cache_0026 : w ∉ ((Wff.classMem (.cv b) (synCnc (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_b, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0027 :
    c ∉ ((synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_z, fresh_c_ne_w,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0028 : c ∉ ((Wff.classMem (.cv b) (synCnc (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_z, or_false, not_false_eq_true])
  have dv_cache_0029 :
    b ∉ ((synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_w,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0030 :
    a ∉ ((synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_w,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0031 : w ∉ ((Wff.classEq X (synCnc (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_X, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0032 :
    z ∉
      ((Wff.imp (.classEq (synCtc A) (synCplc (synCtc B) X))
          (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_X, fresh_z_ne_w,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0033 :
    x ∉
      ((Wff.imp (.classEq (synCtc A) (synCplc (synCtc B) X))
          (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_X, fresh_x_ne_w,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0034 :
    y ∉
      ((Wff.imp (.classEq (synCtc A) (synCplc (synCtc B) X))
          (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_X, fresh_y_ne_w,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0035 : w ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_c, not_false_eq_true])
  have dv_cache_0036 : w ∉ ((Wff.classEq X (synCtc (.cv c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_X, fresh_w_ne_c, or_false, not_false_eq_true])
  have dv_cache_0037 : c ∉ ((synCnc (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_c_ne_w,
          not_false_eq_true])
  have dv_cache_0038 : c ∉ ((Wff.classEq X (synCnc (synCpw1 (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_X_c, fresh_c_ne_w, or_false, not_false_eq_true])
  have p0000 := @gElncs x A dv_cache_0001
  have p0001 := @gElncs y B dv_cache_0002
  have p0002 := @gElncs z X dv_cache_0003
  have p0003 :=
    @gN3anbi123i (.classMem A (synCncs)) (synWex x (.classEq A (synCnc (.cv x))))
      (.classMem B (synCncs)) (synWex y (.classEq B (synCnc (.cv y))))
      (.classMem X (synCncs)) (synWex z (.classEq X (synCnc (.cv z)))) p0000 p0001
      p0002
  have p0004 :=
    @gEeeanv (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
      (.classEq X (synCnc (.cv z))) x y z dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0005 :=
    @gBitr4i
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem X (synCncs)))
      (synW3a (synWex x (.classEq A (synCnc (.cv x))))
        (synWex y (.classEq B (synCnc (.cv y)))) (synWex z (.classEq X (synCnc (.cv z)))))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
              (.classEq X (synCnc (.cv z)))))))
      p0003 p0004
  have p0006 := @gVex x
  have p0007 := @gTcnc (.cv x) p0006
  have p0008 := @gVex y
  have p0009 := @gTcnc (.cv y) p0008
  have p0010 :=
    @gAddceq1i (synCtc (synCnc (.cv y))) (synCnc (synCpw1 (.cv y))) (synCnc (.cv z))
      p0009
  have p0011 :=
    @gEqeq12i (synCtc (synCnc (.cv x))) (synCnc (synCpw1 (.cv x)))
      (synCplc (synCtc (synCnc (.cv y))) (synCnc (.cv z)))
      (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z))) p0007 p0010
  have p0012 :=
    @gEqcom (synCnc (synCpw1 (.cv x)))
      (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z)))
  have p0013 := @gPw1ex (.cv y) p0008
  have p0014 := @gNcelncsi (synCpw1 (.cv y)) p0013
  have p0015 := @gVex z
  have p0016 := @gNcelncsi (.cv z) p0015
  have p0017 := @gNcaddccl (synCnc (synCpw1 (.cv y))) (synCnc (.cv z))
  have p0018 :=
    @gMp2an (.classMem (synCnc (synCpw1 (.cv y))) (synCncs))
      (.classMem (synCnc (.cv z)) (synCncs))
      (.classMem (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z))) (synCncs))
      p0014 p0016 p0017
  have p0019 :=
    @gNcseqnc (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z)))
      (synCpw1 (.cv x))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 :=
    @gN3bitri
      (.classEq (synCtc (synCnc (.cv x)))
        (synCplc (synCtc (synCnc (.cv y))) (synCnc (.cv z))))
      (.classEq (synCnc (synCpw1 (.cv x)))
        (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z))))
      (.classEq (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z)))
        (synCnc (synCpw1 (.cv x))))
      (.classMem (synCpw1 (.cv x)) (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z))))
      p0011 p0012 p0020
  have p0022 :=
    @gEladdc (synCpw1 (.cv x)) (synCnc (synCpw1 (.cv y))) (synCnc (.cv z)) a b
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
  have p0023 := @gVex a
  have p0024 := @gVex b
  have p0025 :=
    @gPw1equn c w (.cv a) (.cv b) (.cv x) dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 p0023 p0024
  have p0026 :=
    @gSimp3 (.classEq (.cv x) (synCun (.cv c) (.cv w)))
      (.classEq (.cv a) (synCpw1 (.cv c))) (.classEq (.cv b) (synCpw1 (.cv w)))
  have p0027 := @gElnc (.cv b) (.cv z)
  have p0028 := @gEnsym (.cv b) (.cv z)
  have p0029 := @gBreq2 (.cv b) (synCpw1 (.cv w)) (.cv z) (synCen)
  have p0030 :=
    @gBiimpcd (.classEq (.cv b) (synCpw1 (.cv w))) (synWbr (.cv z) (synCen) (.cv b))
      (synWbr (.cv z) (synCen) (synCpw1 (.cv w))) p0029
  have p0031 :=
    @gSylbi (synWbr (.cv b) (synCen) (.cv z)) (synWbr (.cv z) (synCen) (.cv b))
      (.imp (.classEq (.cv b) (synCpw1 (.cv w)))
        (synWbr (.cv z) (synCen) (synCpw1 (.cv w))))
      p0028 p0030
  have p0032 :=
    @gSylbi (.classMem (.cv b) (synCnc (.cv z))) (synWbr (.cv b) (synCen) (.cv z))
      (.imp (.classEq (.cv b) (synCpw1 (.cv w)))
        (synWbr (.cv z) (synCen) (synCpw1 (.cv w))))
      p0027 p0031
  have p0033 :=
    @gSyl5
      (synW3a (.classEq (.cv x) (synCun (.cv c) (.cv w)))
        (.classEq (.cv a) (synCpw1 (.cv c))) (.classEq (.cv b) (synCpw1 (.cv w))))
      (.classEq (.cv b) (synCpw1 (.cv w))) (.classMem (.cv b) (synCnc (.cv z)))
      (synWbr (.cv z) (synCen) (synCpw1 (.cv w))) p0026 p0032
  have p0034 :=
    @gEximdv (.classMem (.cv b) (synCnc (.cv z)))
      (synW3a (.classEq (.cv x) (synCun (.cv c) (.cv w)))
        (.classEq (.cv a) (synCpw1 (.cv c))) (.classEq (.cv b) (synCpw1 (.cv w))))
      (synWbr (.cv z) (synCen) (synCpw1 (.cv w))) w dv_cache_0026 p0033
  have p0035 :=
    @gExlimdv (.classMem (.cv b) (synCnc (.cv z)))
      (synWex w (synW3a (.classEq (.cv x) (synCun (.cv c) (.cv w)))
          (.classEq (.cv a) (synCpw1 (.cv c))) (.classEq (.cv b) (synCpw1 (.cv w)))))
      (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))) c dv_cache_0027
      dv_cache_0028 p0034
  have p0036 :=
    @gSyl5bi (.classEq (synCpw1 (.cv x)) (synCun (.cv a) (.cv b)))
      (synWex c (synWex w (synW3a (.classEq (.cv x) (synCun (.cv c) (.cv w)))
            (.classEq (.cv a) (synCpw1 (.cv c))) (.classEq (.cv b) (synCpw1 (.cv w))))))
      (.classMem (.cv b) (synCnc (.cv z)))
      (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))) p0025 p0035
  have p0037 :=
    @gAdantld (.classMem (.cv b) (synCnc (.cv z)))
      (.classEq (synCpw1 (.cv x)) (synCun (.cv a) (.cv b)))
      (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w))))
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0036
  have p0038 :=
    @gRexlimiv
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (synCpw1 (.cv x)) (synCun (.cv a) (.cv b))))
      (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))) b (synCnc (.cv z))
      dv_cache_0029 p0037
  have p0039 :=
    @gRexlimivw
      (synWrex b (synCnc (.cv z)) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (synCpw1 (.cv x)) (synCun (.cv a) (.cv b)))))
      (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))) a
      (synCnc (synCpw1 (.cv y))) dv_cache_0030 p0038
  have p0040 :=
    @gSylbi
      (.classMem (synCpw1 (.cv x)) (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z))))
      (synWrex a (synCnc (synCpw1 (.cv y))) (synWrex b (synCnc (.cv z))
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (synCpw1 (.cv x)) (synCun (.cv a) (.cv b))))))
      (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))) p0022 p0039
  have p0041 :=
    @gSylbi
      (.classEq (synCtc (synCnc (.cv x)))
        (synCplc (synCtc (synCnc (.cv y))) (synCnc (.cv z))))
      (.classMem (synCpw1 (.cv x)) (synCplc (synCnc (synCpw1 (.cv y))) (synCnc (.cv z))))
      (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))) p0021 p0040
  have p0042 := @gTceq A (synCnc (.cv x))
  have p0043 :=
    @gN3ad2ant1 (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
      (.classEq (synCtc A) (synCtc (synCnc (.cv x)))) (.classEq X (synCnc (.cv z)))
      p0042
  have p0044 := @gTceq B (synCnc (.cv y))
  have p0045 :=
    @gAdantr (.classEq B (synCnc (.cv y)))
      (.classEq (synCtc B) (synCtc (synCnc (.cv y)))) (.classEq X (synCnc (.cv z)))
      p0044
  have p0046 := @gSimpr (.classEq B (synCnc (.cv y))) (.classEq X (synCnc (.cv z)))
  have p0047 :=
    @gAddceq12d (synWa (.classEq B (synCnc (.cv y))) (.classEq X (synCnc (.cv z))))
      (synCtc B) (synCtc (synCnc (.cv y))) X (synCnc (.cv z)) p0045 p0046
  have p0048 :=
    @gN3adant1 (.classEq B (synCnc (.cv y))) (.classEq X (synCnc (.cv z)))
      (.classEq (synCplc (synCtc B) X)
        (synCplc (synCtc (synCnc (.cv y))) (synCnc (.cv z))))
      (.classEq A (synCnc (.cv x))) p0047
  have p0049 :=
    @gEqeq12d
      (synW3a (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
        (.classEq X (synCnc (.cv z))))
      (synCtc A) (synCtc (synCnc (.cv x))) (synCplc (synCtc B) X)
      (synCplc (synCtc (synCnc (.cv y))) (synCnc (.cv z))) p0043 p0048
  have p0050 := @gEqeq1 X (synCnc (.cv z)) (synCnc (synCpw1 (.cv w)))
  have p0051 := @gEqnc (.cv z) (synCpw1 (.cv w)) p0015
  have p0052 :=
    @gSyl6bb (.classEq X (synCnc (.cv z))) (.classEq X (synCnc (synCpw1 (.cv w))))
      (.classEq (synCnc (.cv z)) (synCnc (synCpw1 (.cv w))))
      (synWbr (.cv z) (synCen) (synCpw1 (.cv w))) p0050 p0051
  have p0053 :=
    @gExbidv (.classEq X (synCnc (.cv z))) (.classEq X (synCnc (synCpw1 (.cv w))))
      (synWbr (.cv z) (synCen) (synCpw1 (.cv w))) w dv_cache_0031 p0052
  have p0054 :=
    @gN3ad2ant3 (.classEq X (synCnc (.cv z))) (.classEq A (synCnc (.cv x)))
      (synWb (synWex w (.classEq X (synCnc (synCpw1 (.cv w)))))
        (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))))
      (.classEq B (synCnc (.cv y))) p0053
  have p0055 :=
    @gImbi12d
      (synW3a (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
        (.classEq X (synCnc (.cv z))))
      (.classEq (synCtc A) (synCplc (synCtc B) X))
      (.classEq (synCtc (synCnc (.cv x)))
        (synCplc (synCtc (synCnc (.cv y))) (synCnc (.cv z))))
      (synWex w (.classEq X (synCnc (synCpw1 (.cv w)))))
      (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))) p0049 p0054
  have p0056 :=
    @gMpbiri
      (synW3a (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
        (.classEq X (synCnc (.cv z))))
      (.imp (.classEq (synCtc A) (synCplc (synCtc B) X))
        (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))))
      (.imp (.classEq (synCtc (synCnc (.cv x)))
          (synCplc (synCtc (synCnc (.cv y))) (synCnc (.cv z))))
        (synWex w (synWbr (.cv z) (synCen) (synCpw1 (.cv w)))))
      p0041 p0055
  have p0057 :=
    @gExlimiv
      (synW3a (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
        (.classEq X (synCnc (.cv z))))
      (.imp (.classEq (synCtc A) (synCplc (synCtc B) X))
        (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))))
      z dv_cache_0032 p0056
  have p0058 :=
    @gExlimivv
      (synWex z (synW3a (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
          (.classEq X (synCnc (.cv z)))))
      (.imp (.classEq (synCtc A) (synCplc (synCtc B) X))
        (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))))
      x y dv_cache_0033 dv_cache_0034 p0057
  have p0059 :=
    @gSylbi
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem X (synCncs)))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))
              (.classEq X (synCnc (.cv z)))))))
      (.imp (.classEq (synCtc A) (synCplc (synCtc B) X))
        (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))))
      p0005 p0058
  have p0060 :=
    @gImp
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem X (synCncs)))
      (.classEq (synCtc A) (synCplc (synCtc B) X))
      (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))) p0059
  have p0061 := (Nominal.biimpRefl (synWrex c (synCncs) (.classEq X (synCtc (.cv c)))))
  have p0062 := @gElncs w (.cv c) dv_cache_0035
  have p0063 :=
    @gAnbi1i (.classMem (.cv c) (synCncs))
      (synWex w (.classEq (.cv c) (synCnc (.cv w)))) (.classEq X (synCtc (.cv c)))
      p0062
  have p0064 :=
    @gN1941v (.classEq (.cv c) (synCnc (.cv w))) (.classEq X (synCtc (.cv c))) w
      dv_cache_0036
  have p0065 :=
    @gBitr4i (synWa (.classMem (.cv c) (synCncs)) (.classEq X (synCtc (.cv c))))
      (synWa (synWex w (.classEq (.cv c) (synCnc (.cv w)))) (.classEq X (synCtc (.cv c))))
      (synWex w (synWa (.classEq (.cv c) (synCnc (.cv w))) (.classEq X (synCtc (.cv c)))))
      p0063 p0064
  have p0066 :=
    @gExbii (synWa (.classMem (.cv c) (synCncs)) (.classEq X (synCtc (.cv c))))
      (synWex w (synWa (.classEq (.cv c) (synCnc (.cv w))) (.classEq X (synCtc (.cv c)))))
      c p0065
  have p0067 :=
    @gExcom (synWa (.classEq (.cv c) (synCnc (.cv w))) (.classEq X (synCtc (.cv c))))
      c w
  have p0068 := @gNcex (.cv w)
  have p0069 := @gTceq (.cv c) (synCnc (.cv w))
  have p0070 := @gVex w
  have p0071 := @gTcnc (.cv w) p0070
  have p0072 :=
    @gSyl6eq (.classEq (.cv c) (synCnc (.cv w))) (synCtc (.cv c))
      (synCtc (synCnc (.cv w))) (synCnc (synCpw1 (.cv w))) p0069 p0071
  have p0073 :=
    @gEqeq2d (.classEq (.cv c) (synCnc (.cv w))) (synCtc (.cv c))
      (synCnc (synCpw1 (.cv w))) X p0072
  have p0074 :=
    @gCeqsexv (.classEq X (synCtc (.cv c))) (.classEq X (synCnc (synCpw1 (.cv w)))) c
      (synCnc (.cv w)) dv_cache_0037 dv_cache_0038 p0068 p0073
  have p0075 :=
    @gExbii
      (synWex c (synWa (.classEq (.cv c) (synCnc (.cv w))) (.classEq X (synCtc (.cv c)))))
      (.classEq X (synCnc (synCpw1 (.cv w)))) w p0074
  have p0076 :=
    @gBitri
      (synWex c (synWex w
          (synWa (.classEq (.cv c) (synCnc (.cv w))) (.classEq X (synCtc (.cv c))))))
      (synWex w (synWex c
          (synWa (.classEq (.cv c) (synCnc (.cv w))) (.classEq X (synCtc (.cv c))))))
      (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))) p0067 p0075
  have p0077 :=
    @gN3bitri (synWrex c (synCncs) (.classEq X (synCtc (.cv c))))
      (synWex c (synWa (.classMem (.cv c) (synCncs)) (.classEq X (synCtc (.cv c)))))
      (synWex c (synWex w
          (synWa (.classEq (.cv c) (synCnc (.cv w))) (.classEq X (synCtc (.cv c))))))
      (synWex w (.classEq X (synCnc (synCpw1 (.cv w))))) p0061 p0066 p0076
  have p0078 :=
    @gSylibr
      (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem X (synCncs))) (.classEq (synCtc A) (synCplc (synCtc B) X)))
      (synWex w (.classEq X (synCnc (synCpw1 (.cv w)))))
      (synWrex c (synCncs) (.classEq X (synCtc (.cv c)))) p0060 p0077
  exact p0078


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part056`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tlecg`. -/
@[expose]
noncomputable def gTlecg (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWb (synWbr M (synClec) N) (synWbr (synCtc M) (synClec) (synCtc N)))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_M, not_false_eq_true])
  have dv_cache_0002 : p ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_N, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((synWbr (synCtc M) (synClec) (synCtc N))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_p_not_M, fresh_p_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : p ∉ ((Wff.classMem M (synCncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_p_not_M, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((synCtc M)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_p_not_M,
          not_false_eq_true])
  have dv_cache_0006 : p ∉ ((synCtc N)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_p_not_N,
          not_false_eq_true])
  have dv_cache_0007 : q ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_p, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((synWbr M (synClec) N)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    q ∉
      ((synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
          (.classEq (synCtc N) (synCplc (synCtc M) (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_not_M, fresh_q_not_N, fresh_q_ne_p,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((synWbr M (synClec) N)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_p_not_M, fresh_p_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    p ∉ ((synWa (.classMem M (synCncs)) (.classMem N (synCncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_p_not_M, fresh_p_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gDflec2 M N p dv_cache_0001 dv_cache_0002
  have p0001 := @gTccl M
  have p0002 := @gTccl (.cv p)
  have p0003 := @gAddlecncs (synCtc M) (synCtc (.cv p))
  have p0004 :=
    @gSyl2an (.classMem M (synCncs)) (.classMem (synCtc M) (synCncs))
      (.classMem (synCtc (.cv p)) (synCncs))
      (synWbr (synCtc M) (synClec) (synCplc (synCtc M) (synCtc (.cv p))))
      (.classMem (.cv p) (synCncs)) p0001 p0002 p0003
  have p0005 := @gTcdi M (.cv p)
  have p0006 :=
    @gBreqtrrd (synWa (.classMem M (synCncs)) (.classMem (.cv p) (synCncs)))
      (synCtc M) (synCplc (synCtc M) (synCtc (.cv p))) (synCtc (synCplc M (.cv p)))
      (synClec) p0004 p0005
  have p0007 := @gTceq N (synCplc M (.cv p))
  have p0008 :=
    @gBreq2d (.classEq N (synCplc M (.cv p))) (synCtc N) (synCtc (synCplc M (.cv p)))
      (synCtc M) (synClec) p0007
  have p0009 :=
    @gSyl5ibrcom (synWa (.classMem M (synCncs)) (.classMem (.cv p) (synCncs)))
      (synWbr (synCtc M) (synClec) (synCtc N)) (.classEq N (synCplc M (.cv p)))
      (synWbr (synCtc M) (synClec) (synCtc (synCplc M (.cv p)))) p0006 p0008
  have p0010 :=
    @gRexlimdva (.classMem M (synCncs)) (.classEq N (synCplc M (.cv p)))
      (synWbr (synCtc M) (synClec) (synCtc N)) p (synCncs) dv_cache_0003
      dv_cache_0004 p0009
  have p0011 :=
    @gAdantr (.classMem M (synCncs))
      (.imp (synWrex p (synCncs) (.classEq N (synCplc M (.cv p))))
        (synWbr (synCtc M) (synClec) (synCtc N)))
      (.classMem N (synCncs)) p0010
  have p0012 :=
    @gSylbid (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWbr M (synClec) N) (synWrex p (synCncs) (.classEq N (synCplc M (.cv p))))
      (synWbr (synCtc M) (synClec) (synCtc N)) p0000 p0011
  have p0013 := @gTccl N
  have p0014 := @gDflec2 (synCtc M) (synCtc N) p dv_cache_0005 dv_cache_0006
  have p0015 :=
    @gSyl2an (.classMem M (synCncs)) (.classMem (synCtc M) (synCncs))
      (.classMem (synCtc N) (synCncs))
      (synWb (synWbr (synCtc M) (synClec) (synCtc N))
        (synWrex p (synCncs) (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))))
      (.classMem N (synCncs)) p0001 p0013 p0014
  have p0016 :=
    @gSimplr (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWa (.classMem (.cv p) (synCncs))
        (.classEq (synCtc N) (synCplc (synCtc M) (.cv p))))
  have p0017 :=
    @gSimpll (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWa (.classMem (.cv p) (synCncs))
        (.classEq (synCtc N) (synCplc (synCtc M) (.cv p))))
  have p0018 :=
    @gSimprl (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classMem (.cv p) (synCncs)) (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
  have p0019 :=
    @gSimprr (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classMem (.cv p) (synCncs)) (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
  have p0020 := @gTaddc N M (.cv p) q dv_cache_0007
  have p0021 :=
    @gSyl31anc
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWa (.classMem (.cv p) (synCncs))
          (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))))
      (.classMem N (synCncs)) (.classMem M (synCncs)) (.classMem (.cv p) (synCncs))
      (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
      (synWrex q (synCncs) (.classEq (.cv p) (synCtc (.cv q)))) p0016 p0017 p0018 p0019
      p0020
  have p0022 := @gAddceq2 (.cv p) (synCtc (.cv q)) (synCtc M)
  have p0023 :=
    @gEqeq2d (.classEq (.cv p) (synCtc (.cv q))) (synCplc (synCtc M) (.cv p))
      (synCplc (synCtc M) (synCtc (.cv q))) (synCtc N) p0022
  have p0024 :=
    @gBiimpac (.classEq (.cv p) (synCtc (.cv q)))
      (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
      (.classEq (synCtc N) (synCplc (synCtc M) (synCtc (.cv q)))) p0023
  have p0025 := @gTcdi M (.cv q)
  have p0026 :=
    @gAdantlr (.classMem M (synCncs)) (.classMem (.cv q) (synCncs))
      (.classEq (synCtc (synCplc M (.cv q))) (synCplc (synCtc M) (synCtc (.cv q))))
      (.classMem N (synCncs)) p0025
  have p0027 :=
    @gEqeq2d
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (synCtc (synCplc M (.cv q))) (synCplc (synCtc M) (synCtc (.cv q))) (synCtc N)
      p0026
  have p0028 :=
    @gSimplr (.classMem M (synCncs)) (.classMem N (synCncs))
      (.classMem (.cv q) (synCncs))
  have p0029 := @gNcaddccl M (.cv q)
  have p0030 :=
    @gAdantlr (.classMem M (synCncs)) (.classMem (.cv q) (synCncs))
      (.classMem (synCplc M (.cv q)) (synCncs)) (.classMem N (synCncs)) p0029
  have p0031 := @gTc11 N (synCplc M (.cv q))
  have p0032 :=
    @gSyl2anc
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (.classMem N (synCncs)) (.classMem (synCplc M (.cv q)) (synCncs))
      (synWb (.classEq (synCtc N) (synCtc (synCplc M (.cv q))))
        (.classEq N (synCplc M (.cv q))))
      p0028 p0030 p0031
  have p0033 := @gAddlecncs M (.cv q)
  have p0034 := @gBreq2 N (synCplc M (.cv q)) M (synClec)
  have p0035 :=
    @gSyl5ibrcom (synWa (.classMem M (synCncs)) (.classMem (.cv q) (synCncs)))
      (synWbr M (synClec) N) (.classEq N (synCplc M (.cv q)))
      (synWbr M (synClec) (synCplc M (.cv q))) p0033 p0034
  have p0036 :=
    @gAdantlr (.classMem M (synCncs)) (.classMem (.cv q) (synCncs))
      (.imp (.classEq N (synCplc M (.cv q))) (synWbr M (synClec) N))
      (.classMem N (synCncs)) p0035
  have p0037 :=
    @gSylbid
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (.classEq (synCtc N) (synCtc (synCplc M (.cv q))))
      (.classEq N (synCplc M (.cv q))) (synWbr M (synClec) N) p0032 p0036
  have p0038 :=
    @gSylbird
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (.classEq (synCtc N) (synCplc (synCtc M) (synCtc (.cv q))))
      (.classEq (synCtc N) (synCtc (synCplc M (.cv q)))) (synWbr M (synClec) N) p0027
      p0037
  have p0039 :=
    @gSyl5
      (synWa (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
        (.classEq (.cv p) (synCtc (.cv q))))
      (.classEq (synCtc N) (synCplc (synCtc M) (synCtc (.cv q))))
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (synWbr M (synClec) N) p0024 p0038
  have p0040 :=
    @gExpdimp
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
      (.classEq (.cv p) (synCtc (.cv q))) (synWbr M (synClec) N) p0039
  have p0041 :=
    @gAn32s (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classMem (.cv q) (synCncs)) (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
      (.imp (.classEq (.cv p) (synCtc (.cv q))) (synWbr M (synClec) N)) p0040
  have p0042 :=
    @gRexlimdva
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (.classEq (synCtc N) (synCplc (synCtc M) (.cv p))))
      (.classEq (.cv p) (synCtc (.cv q))) (synWbr M (synClec) N) q (synCncs)
      dv_cache_0008 dv_cache_0009 p0041
  have p0043 :=
    @gAdantrl (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
      (.imp (synWrex q (synCncs) (.classEq (.cv p) (synCtc (.cv q))))
        (synWbr M (synClec) N))
      (.classMem (.cv p) (synCncs)) p0042
  have p0044 :=
    @gMpd
      (synWa (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (synWa (.classMem (.cv p) (synCncs))
          (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))))
      (synWrex q (synCncs) (.classEq (.cv p) (synCtc (.cv q))))
      (synWbr M (synClec) N) p0021 p0043
  have p0045 :=
    @gExpr (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classMem (.cv p) (synCncs)) (.classEq (synCtc N) (synCplc (synCtc M) (.cv p)))
      (synWbr M (synClec) N) p0044
  have p0046 :=
    @gRexlimdva (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classEq (synCtc N) (synCplc (synCtc M) (.cv p))) (synWbr M (synClec) N) p
      (synCncs) dv_cache_0010 dv_cache_0011 p0045
  have p0047 :=
    @gSylbid (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWbr (synCtc M) (synClec) (synCtc N))
      (synWrex p (synCncs) (.classEq (synCtc N) (synCplc (synCtc M) (.cv p))))
      (synWbr M (synClec) N) p0015 p0046
  have p0048 :=
    @gImpbid (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWbr M (synClec) N) (synWbr (synCtc M) (synClec) (synCtc N)) p0012 p0047
  exact p0048


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part057`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_letc`. -/
@[expose]
noncomputable def gLetc (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
          (synWbr M (synClec) (synCtc N)))
        (synWrex p (synCncs) (.classEq M (synCtc (.cv p))))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  let c : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  let y : Var := freshVar proofSupport 5
  let n : Var := freshVar proofSupport 6
  let m : Var := freshVar proofSupport 7
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_p : a ≠ p := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_a : p ≠ a := Ne.symm fresh_a_ne_p
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_p : b ≠ p := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_c_not_M : c ∉ M.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_N : c ∉ N.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_ne_p : c ≠ p := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_ne_p : x ≠ p := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_n_ne_p : n ≠ p := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_n : p ≠ n := Ne.symm fresh_n_ne_p
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_m_ne_p : m ≠ p := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_a : q ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_q : a ≠ q := Ne.symm fresh_q_ne_a
  have fresh_q_ne_b : q ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_q : b ≠ q := Ne.symm fresh_q_ne_b
  have fresh_q_ne_c : q ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_c_ne_q : c ≠ q := Ne.symm fresh_q_ne_c
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_n : a ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_m_ne_a : m ≠ a := Ne.symm fresh_a_ne_m
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_ne_n : b ≠ n :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_n_ne_b : n ≠ b := Ne.symm fresh_b_ne_n
  have fresh_b_ne_m : b ≠ m :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_m_ne_b : m ≠ b := Ne.symm fresh_b_ne_m
  have fresh_c_ne_x : c ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_y : c ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_y_ne_c : y ≠ c := Ne.symm fresh_c_ne_y
  have fresh_c_ne_n : c ≠ n :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_n_ne_c : n ≠ c := Ne.symm fresh_c_ne_n
  have fresh_c_ne_m : c ≠ m :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_m_ne_c : m ≠ c := Ne.symm fresh_c_ne_m
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_x_ne_m : x ≠ m :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_m_ne_x : m ≠ x := Ne.symm fresh_x_ne_m
  have fresh_y_ne_n : y ≠ n :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_y_ne_m : y ≠ m :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_m_ne_y : m ≠ y := Ne.symm fresh_y_ne_m
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have dv_cache_0001 : q ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_M, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCtc N)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_q_not_N,
          not_false_eq_true])
  have dv_cache_0003 : a ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_M, not_false_eq_true])
  have dv_cache_0004 : b ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_N, not_false_eq_true])
  have dv_cache_0005 : c ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_q, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((Wff.classEq (.cv q) (synCnc (.cv c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_q, fresh_a_ne_c, or_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((Wff.classEq (.cv q) (synCnc (.cv c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_q, fresh_b_ne_c, or_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Wff.classEq M (synCnc (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_M, fresh_b_ne_a, or_false, not_false_eq_true])
  have dv_cache_0009 : c ∉ ((Wff.classEq M (synCnc (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_not_M, fresh_c_ne_a, or_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((Wff.classEq N (synCnc (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_N, fresh_a_ne_b, or_false, not_false_eq_true])
  have dv_cache_0011 : c ∉ ((Wff.classEq N (synCnc (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_not_N, fresh_c_ne_b, or_false, not_false_eq_true])
  have dv_cache_0012 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0013 : a ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0014 : x ∉ ((synCpw1 (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_b,
          not_false_eq_true])
  have dv_cache_0015 : y ∉ ((synCpw1 (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_b,
          not_false_eq_true])
  have dv_cache_0016 : x ∉ ((synCnc (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
          not_false_eq_true])
  have dv_cache_0017 : y ∉ ((synCnc (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_a,
          not_false_eq_true])
  have dv_cache_0018 : x ∉ ((synCnc (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_c,
          not_false_eq_true])
  have dv_cache_0019 : y ∉ ((synCnc (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_c,
          not_false_eq_true])
  have dv_cache_0020 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0021 : n ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_x, not_false_eq_true])
  have dv_cache_0022 : m ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_m_ne_x, not_false_eq_true])
  have dv_cache_0023 : n ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_y, not_false_eq_true])
  have dv_cache_0024 : m ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_m_ne_y, not_false_eq_true])
  have dv_cache_0025 : n ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_b, not_false_eq_true])
  have dv_cache_0026 : m ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_m_ne_b, not_false_eq_true])
  have dv_cache_0027 : n ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have dv_cache_0028 : p ∉ ((synCnc (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_p_ne_n,
          not_false_eq_true])
  have dv_cache_0029 : p ∉ ((synCncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0030 :
    p ∉ ((Wff.classEq (synCnc (.cv a)) (synCnc (synCpw1 (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_n, or_false, not_false_eq_true])
  have dv_cache_0031 :
    n ∉
      ((Wff.imp (synWa (synWa (.classMem (.cv x) (synCnc (.cv a)))
              (.classMem (.cv y) (synCnc (.cv c))))
            (.classEq (synCin (.cv x) (.cv y)) (synC0)))
          (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_x, fresh_n_ne_a,
          fresh_n_ne_y, fresh_n_ne_c, fresh_n_ne_p, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0032 :
    m ∉
      ((Wff.imp (synWa (synWa (.classMem (.cv x) (synCnc (.cv a)))
              (.classMem (.cv y) (synCnc (.cv c))))
            (.classEq (synCin (.cv x) (.cv y)) (synC0)))
          (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_ne_x, fresh_m_ne_a,
          fresh_m_ne_y, fresh_m_ne_c, fresh_m_ne_p, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0033 :
    x ∉ ((synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0034 :
    y ∉ ((synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0035 : p ∉ ((Wff.classEq M (synCnc (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_M_p, fresh_p_ne_a, or_false, not_false_eq_true])
  have dv_cache_0036 :
    c ∉
      ((Wff.imp (.classEq (synCtc N) (synCplc M (.cv q)))
          (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_not_N, fresh_c_not_M,
          fresh_c_ne_q, fresh_c_ne_p, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0037 :
    a ∉
      ((Wff.imp (.classEq (synCtc N) (synCplc M (.cv q)))
          (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_N, fresh_a_not_M,
          fresh_a_ne_q, fresh_a_ne_p, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0038 :
    b ∉
      ((Wff.imp (.classEq (synCtc N) (synCplc M (.cv q)))
          (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_N, fresh_b_not_M,
          fresh_b_ne_q, fresh_b_ne_p, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0039 : q ∉ ((synWrex p (synCncs) (.classEq M (synCtc (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0040 :
    q ∉ ((synWa (.classMem M (synCncs)) (.classMem N (synCncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gTccl N
  have p0001 := @gDflec2 M (synCtc N) q dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gSylan2 (.classMem N (synCncs)) (.classMem M (synCncs))
      (.classMem (synCtc N) (synCncs))
      (synWb (synWbr M (synClec) (synCtc N))
        (synWrex q (synCncs) (.classEq (synCtc N) (synCplc M (.cv q)))))
      p0000 p0001
  have p0003 := @gElncs a M dv_cache_0003
  have p0004 := @gElncs b N dv_cache_0004
  have p0005 := @gElncs c (.cv q) dv_cache_0005
  have p0006 :=
    @gN3anbi123i (.classMem M (synCncs)) (synWex a (.classEq M (synCnc (.cv a))))
      (.classMem N (synCncs)) (synWex b (.classEq N (synCnc (.cv b))))
      (.classMem (.cv q) (synCncs)) (synWex c (.classEq (.cv q) (synCnc (.cv c))))
      p0003 p0004 p0005
  have p0007 :=
    @gEeeanv (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
      (.classEq (.cv q) (synCnc (.cv c))) a b c dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0008 :=
    @gBitr4i
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (.classMem (.cv q) (synCncs)))
      (synW3a (synWex a (.classEq M (synCnc (.cv a))))
        (synWex b (.classEq N (synCnc (.cv b))))
        (synWex c (.classEq (.cv q) (synCnc (.cv c)))))
      (synWex a (synWex b (synWex c
            (synW3a (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
              (.classEq (.cv q) (synCnc (.cv c)))))))
      p0006 p0007
  have p0009 :=
    @gEqcom (synCnc (synCpw1 (.cv b))) (synCplc (synCnc (.cv a)) (synCnc (.cv c)))
  have p0010 := @gVex a
  have p0011 := @gNcelncsi (.cv a) p0010
  have p0012 := @gVex c
  have p0013 := @gNcelncsi (.cv c) p0012
  have p0014 := @gNcaddccl (synCnc (.cv a)) (synCnc (.cv c))
  have p0015 :=
    @gMp2an (.classMem (synCnc (.cv a)) (synCncs))
      (.classMem (synCnc (.cv c)) (synCncs))
      (.classMem (synCplc (synCnc (.cv a)) (synCnc (.cv c))) (synCncs)) p0011 p0013
      p0014
  have p0016 :=
    @gNcseqnc (synCplc (synCnc (.cv a)) (synCnc (.cv c))) (synCpw1 (.cv b))
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @gBitri
      (.classEq (synCnc (synCpw1 (.cv b))) (synCplc (synCnc (.cv a)) (synCnc (.cv c))))
      (.classEq (synCplc (synCnc (.cv a)) (synCnc (.cv c))) (synCnc (synCpw1 (.cv b))))
      (.classMem (synCpw1 (.cv b)) (synCplc (synCnc (.cv a)) (synCnc (.cv c)))) p0009
      p0017
  have p0019 :=
    @gEladdc (synCpw1 (.cv b)) (synCnc (.cv a)) (synCnc (.cv c)) x y dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0020 := @gVex x
  have p0021 := @gVex y
  have p0022 :=
    @gPw1equn n m (.cv x) (.cv y) (.cv b) dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 p0020 p0021
  have p0023 := @gEleq1 (.cv x) (synCpw1 (.cv n)) (synCnc (.cv a))
  have p0024 := @gEleq1 (.cv y) (synCpw1 (.cv m)) (synCnc (.cv c))
  have p0025 :=
    @gBi2anan9 (.classEq (.cv x) (synCpw1 (.cv n)))
      (.classMem (.cv x) (synCnc (.cv a)))
      (.classMem (synCpw1 (.cv n)) (synCnc (.cv a)))
      (.classEq (.cv y) (synCpw1 (.cv m))) (.classMem (.cv y) (synCnc (.cv c)))
      (.classMem (synCpw1 (.cv m)) (synCnc (.cv c))) p0023 p0024
  have p0026 := @gIneq12 (.cv x) (synCpw1 (.cv n)) (.cv y) (synCpw1 (.cv m))
  have p0027 :=
    @gEqeq1d
      (synWa (.classEq (.cv x) (synCpw1 (.cv n))) (.classEq (.cv y) (synCpw1 (.cv m))))
      (synCin (.cv x) (.cv y)) (synCin (synCpw1 (.cv n)) (synCpw1 (.cv m))) (synC0)
      p0026
  have p0028 :=
    @gAnbi12d
      (synWa (.classEq (.cv x) (synCpw1 (.cv n))) (.classEq (.cv y) (synCpw1 (.cv m))))
      (synWa (.classMem (.cv x) (synCnc (.cv a))) (.classMem (.cv y) (synCnc (.cv c))))
      (synWa (.classMem (synCpw1 (.cv n)) (synCnc (.cv a)))
        (.classMem (synCpw1 (.cv m)) (synCnc (.cv c))))
      (.classEq (synCin (.cv x) (.cv y)) (synC0))
      (.classEq (synCin (synCpw1 (.cv n)) (synCpw1 (.cv m))) (synC0)) p0025 p0027
  have p0029 := @gNcseqnc (synCnc (.cv a)) (synCpw1 (.cv n))
  have p0030 := Nominal.mp p0011 p0029
  have p0031 := @gVex n
  have p0032 := @gNcelncsi (.cv n) p0031
  have p0033 := @gTceq (.cv p) (synCnc (.cv n))
  have p0034 := @gTcnc (.cv n) p0031
  have p0035 :=
    @gSyl6eq (.classEq (.cv p) (synCnc (.cv n))) (synCtc (.cv p))
      (synCtc (synCnc (.cv n))) (synCnc (synCpw1 (.cv n))) p0033 p0034
  have p0036 :=
    @gEqeq2d (.classEq (.cv p) (synCnc (.cv n))) (synCtc (.cv p))
      (synCnc (synCpw1 (.cv n))) (synCnc (.cv a)) p0035
  have p0037 :=
    @gRspcev (.classEq (synCnc (.cv a)) (synCtc (.cv p)))
      (.classEq (synCnc (.cv a)) (synCnc (synCpw1 (.cv n)))) p (synCnc (.cv n))
      (synCncs) dv_cache_0028 dv_cache_0029 dv_cache_0030 p0036
  have p0038 :=
    @gMpan (.classMem (synCnc (.cv n)) (synCncs))
      (.classEq (synCnc (.cv a)) (synCnc (synCpw1 (.cv n))))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0032 p0037
  have p0039 :=
    @gSylbir (.classMem (synCpw1 (.cv n)) (synCnc (.cv a)))
      (.classEq (synCnc (.cv a)) (synCnc (synCpw1 (.cv n))))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0030 p0038
  have p0040 :=
    @gAd2antrr (.classMem (synCpw1 (.cv n)) (synCnc (.cv a)))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p))))
      (.classMem (synCpw1 (.cv m)) (synCnc (.cv c)))
      (.classEq (synCin (synCpw1 (.cv n)) (synCpw1 (.cv m))) (synC0)) p0039
  have p0041 :=
    @gSyl6bi
      (synWa (.classEq (.cv x) (synCpw1 (.cv n))) (.classEq (.cv y) (synCpw1 (.cv m))))
      (synWa (synWa (.classMem (.cv x) (synCnc (.cv a)))
          (.classMem (.cv y) (synCnc (.cv c)))) (.classEq (synCin (.cv x) (.cv y)) (synC0)))
      (synWa (synWa (.classMem (synCpw1 (.cv n)) (synCnc (.cv a)))
          (.classMem (synCpw1 (.cv m)) (synCnc (.cv c))))
        (.classEq (synCin (synCpw1 (.cv n)) (synCpw1 (.cv m))) (synC0)))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0028 p0040
  have p0042 :=
    @gN3adant1 (.classEq (.cv x) (synCpw1 (.cv n)))
      (.classEq (.cv y) (synCpw1 (.cv m)))
      (.imp (synWa (synWa (.classMem (.cv x) (synCnc (.cv a)))
            (.classMem (.cv y) (synCnc (.cv c))))
          (.classEq (synCin (.cv x) (.cv y)) (synC0)))
        (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))))
      (.classEq (.cv b) (synCun (.cv n) (.cv m))) p0041
  have p0043 :=
    @gExlimivv
      (synW3a (.classEq (.cv b) (synCun (.cv n) (.cv m)))
        (.classEq (.cv x) (synCpw1 (.cv n))) (.classEq (.cv y) (synCpw1 (.cv m))))
      (.imp (synWa (synWa (.classMem (.cv x) (synCnc (.cv a)))
            (.classMem (.cv y) (synCnc (.cv c))))
          (.classEq (synCin (.cv x) (.cv y)) (synC0)))
        (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))))
      n m dv_cache_0031 dv_cache_0032 p0042
  have p0044 :=
    @gCom12
      (synWex n (synWex m (synW3a (.classEq (.cv b) (synCun (.cv n) (.cv m)))
            (.classEq (.cv x) (synCpw1 (.cv n))) (.classEq (.cv y) (synCpw1 (.cv m))))))
      (synWa (synWa (.classMem (.cv x) (synCnc (.cv a)))
          (.classMem (.cv y) (synCnc (.cv c)))) (.classEq (synCin (.cv x) (.cv y)) (synC0)))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0043
  have p0045 :=
    @gSyl5bi (.classEq (synCpw1 (.cv b)) (synCun (.cv x) (.cv y)))
      (synWex n (synWex m (synW3a (.classEq (.cv b) (synCun (.cv n) (.cv m)))
            (.classEq (.cv x) (synCpw1 (.cv n))) (.classEq (.cv y) (synCpw1 (.cv m))))))
      (synWa (synWa (.classMem (.cv x) (synCnc (.cv a)))
          (.classMem (.cv y) (synCnc (.cv c)))) (.classEq (synCin (.cv x) (.cv y)) (synC0)))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0022 p0044
  have p0046 :=
    @gExpimpd
      (synWa (.classMem (.cv x) (synCnc (.cv a))) (.classMem (.cv y) (synCnc (.cv c))))
      (.classEq (synCin (.cv x) (.cv y)) (synC0))
      (.classEq (synCpw1 (.cv b)) (synCun (.cv x) (.cv y)))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0045
  have p0047 :=
    @gRexlimivv
      (synWa (.classEq (synCin (.cv x) (.cv y)) (synC0))
        (.classEq (synCpw1 (.cv b)) (synCun (.cv x) (.cv y))))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) x y
      (synCnc (.cv a)) (synCnc (.cv c)) dv_cache_0017 dv_cache_0033 dv_cache_0034
      dv_cache_0020 p0046
  have p0048 :=
    @gSylbi (.classMem (synCpw1 (.cv b)) (synCplc (synCnc (.cv a)) (synCnc (.cv c))))
      (synWrex x (synCnc (.cv a)) (synWrex y (synCnc (.cv c))
          (synWa (.classEq (synCin (.cv x) (.cv y)) (synC0))
            (.classEq (synCpw1 (.cv b)) (synCun (.cv x) (.cv y))))))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0019 p0047
  have p0049 :=
    @gSylbi
      (.classEq (synCnc (synCpw1 (.cv b))) (synCplc (synCnc (.cv a)) (synCnc (.cv c))))
      (.classMem (synCpw1 (.cv b)) (synCplc (synCnc (.cv a)) (synCnc (.cv c))))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0018 p0048
  have p0050 := @gTceq N (synCnc (.cv b))
  have p0051 := @gVex b
  have p0052 := @gTcnc (.cv b) p0051
  have p0053 :=
    @gSyl6eq (.classEq N (synCnc (.cv b))) (synCtc N) (synCtc (synCnc (.cv b)))
      (synCnc (synCpw1 (.cv b))) p0050 p0052
  have p0054 :=
    @gN3ad2ant2 (.classEq N (synCnc (.cv b))) (.classEq M (synCnc (.cv a)))
      (.classEq (synCtc N) (synCnc (synCpw1 (.cv b))))
      (.classEq (.cv q) (synCnc (.cv c))) p0053
  have p0055 := @gAddceq12 M (.cv q) (synCnc (.cv a)) (synCnc (.cv c))
  have p0056 :=
    @gN3adant2 (.classEq M (synCnc (.cv a))) (.classEq (.cv q) (synCnc (.cv c)))
      (.classEq (synCplc M (.cv q)) (synCplc (synCnc (.cv a)) (synCnc (.cv c))))
      (.classEq N (synCnc (.cv b))) p0055
  have p0057 :=
    @gEqeq12d
      (synW3a (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
        (.classEq (.cv q) (synCnc (.cv c))))
      (synCtc N) (synCnc (synCpw1 (.cv b))) (synCplc M (.cv q))
      (synCplc (synCnc (.cv a)) (synCnc (.cv c))) p0054 p0056
  have p0058 := @gEqeq1 M (synCnc (.cv a)) (synCtc (.cv p))
  have p0059 :=
    @gRexbidv (.classEq M (synCnc (.cv a))) (.classEq M (synCtc (.cv p)))
      (.classEq (synCnc (.cv a)) (synCtc (.cv p))) p (synCncs) dv_cache_0035 p0058
  have p0060 :=
    @gN3ad2ant1 (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
      (synWb (synWrex p (synCncs) (.classEq M (synCtc (.cv p))))
        (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))))
      (.classEq (.cv q) (synCnc (.cv c))) p0059
  have p0061 :=
    @gImbi12d
      (synW3a (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
        (.classEq (.cv q) (synCnc (.cv c))))
      (.classEq (synCtc N) (synCplc M (.cv q)))
      (.classEq (synCnc (synCpw1 (.cv b))) (synCplc (synCnc (.cv a)) (synCnc (.cv c))))
      (synWrex p (synCncs) (.classEq M (synCtc (.cv p))))
      (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))) p0057 p0060
  have p0062 :=
    @gMpbiri
      (synW3a (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
        (.classEq (.cv q) (synCnc (.cv c))))
      (.imp (.classEq (synCtc N) (synCplc M (.cv q)))
        (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))))
      (.imp (.classEq (synCnc (synCpw1 (.cv b)))
          (synCplc (synCnc (.cv a)) (synCnc (.cv c))))
        (synWrex p (synCncs) (.classEq (synCnc (.cv a)) (synCtc (.cv p)))))
      p0049 p0061
  have p0063 :=
    @gExlimiv
      (synW3a (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
        (.classEq (.cv q) (synCnc (.cv c))))
      (.imp (.classEq (synCtc N) (synCplc M (.cv q)))
        (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))))
      c dv_cache_0036 p0062
  have p0064 :=
    @gExlimivv
      (synWex c (synW3a (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
          (.classEq (.cv q) (synCnc (.cv c)))))
      (.imp (.classEq (synCtc N) (synCplc M (.cv q)))
        (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))))
      a b dv_cache_0037 dv_cache_0038 p0063
  have p0065 :=
    @gSylbi
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (.classMem (.cv q) (synCncs)))
      (synWex a (synWex b (synWex c
            (synW3a (.classEq M (synCnc (.cv a))) (.classEq N (synCnc (.cv b)))
              (.classEq (.cv q) (synCnc (.cv c)))))))
      (.imp (.classEq (synCtc N) (synCplc M (.cv q)))
        (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))))
      p0008 p0064
  have p0066 :=
    @gN3expa (.classMem M (synCncs)) (.classMem N (synCncs))
      (.classMem (.cv q) (synCncs))
      (.imp (.classEq (synCtc N) (synCplc M (.cv q)))
        (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))))
      p0065
  have p0067 :=
    @gRexlimdva (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.classEq (synCtc N) (synCplc M (.cv q)))
      (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))) q (synCncs) dv_cache_0039
      dv_cache_0040 p0066
  have p0068 :=
    @gSylbid (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (synWbr M (synClec) (synCtc N))
      (synWrex q (synCncs) (.classEq (synCtc N) (synCplc M (.cv q))))
      (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))) p0002 p0067
  have p0069 :=
    @gN3impia (.classMem M (synCncs)) (.classMem N (synCncs))
      (synWbr M (synClec) (synCtc N))
      (synWrex p (synCncs) (.classEq M (synCtc (.cv p)))) p0068
  exact p0069


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part058`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tlenc1c`. -/
@[expose]
noncomputable def gTlenc1c (M : Class) :
    Nominal.NPrf
      (.imp (.classMem M (synCncs)) (synWbr (synCtc M) (synClec) (synCnc (synC1c)))) :=
  by
  let proofSupport : Finset Var := M.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_M, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCpw1 (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCpw1 (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
          not_false_eq_true])
  have dv_cache_0004 : z ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCnc (synCpw1 (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synCnc (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0007 : z ∉ ((synCnc (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWss (synCpw1 (.cv x)) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synWss (synCpw1 (.cv x)) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : x ∉ ((synWbr (synCtc M) (synClec) (synCnc (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_x_not_M, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gElncs x M dv_cache_0001
  have p0001 := @gTceq M (synCnc (.cv x))
  have p0002 := @gVex x
  have p0003 := @gTcnc (.cv x) p0002
  have p0004 :=
    @gSyl6eq (.classEq M (synCnc (.cv x))) (synCtc M) (synCtc (synCnc (.cv x)))
      (synCnc (synCpw1 (.cv x))) p0001 p0003
  have p0005 := @gPw1ex (.cv x) p0002
  have p0006 := @gNcid (synCpw1 (.cv x)) p0005
  have p0007 := @gN1cex
  have p0008 := @gNcid (synC1c) p0007
  have p0009 := @gPw1ss1c (.cv x)
  have p0010 := @gSseq1 (.cv y) (synCpw1 (.cv x)) (.cv z)
  have p0011 := @gSseq2 (.cv z) (synC1c) (synCpw1 (.cv x))
  have p0012 :=
    @gRspc2ev (synWss (.cv y) (.cv z)) (synWss (synCpw1 (.cv x)) (synC1c))
      (synWss (synCpw1 (.cv x)) (.cv z)) y z (synCpw1 (.cv x)) (synC1c)
      (synCnc (synCpw1 (.cv x))) (synCnc (synC1c)) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0010 p0011
  have p0013 :=
    @gMp3an (.classMem (synCpw1 (.cv x)) (synCnc (synCpw1 (.cv x))))
      (.classMem (synC1c) (synCnc (synC1c))) (synWss (synCpw1 (.cv x)) (synC1c))
      (synWrex y (synCnc (synCpw1 (.cv x)))
        (synWrex z (synCnc (synC1c)) (synWss (.cv y) (.cv z))))
      p0006 p0008 p0009 p0012
  have p0014 := @gNcex (synCpw1 (.cv x))
  have p0015 := @gNcex (synC1c)
  have p0016 :=
    @gBrlec y z (synCnc (synCpw1 (.cv x))) (synCnc (synC1c)) dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0010 p0014 p0015
  have p0017 :=
    @gMpbir (synWbr (synCnc (synCpw1 (.cv x))) (synClec) (synCnc (synC1c)))
      (synWrex y (synCnc (synCpw1 (.cv x)))
        (synWrex z (synCnc (synC1c)) (synWss (.cv y) (.cv z))))
      p0013 p0016
  have p0018 :=
    @gSyl6eqbr (.classEq M (synCnc (.cv x))) (synCtc M) (synCnc (synCpw1 (.cv x)))
      (synCnc (synC1c)) (synClec) p0004 p0017
  have p0019 :=
    @gExlimiv (.classEq M (synCnc (.cv x)))
      (synWbr (synCtc M) (synClec) (synCnc (synC1c))) x dv_cache_0011 p0018
  have p0020 :=
    @gSylbi (.classMem M (synCncs)) (synWex x (.classEq M (synCnc (.cv x))))
      (synWbr (synCtc M) (synClec) (synCnc (synC1c))) p0000 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_n_1ne0c`. -/
@[expose]
noncomputable def gN1ne0c : Nominal.NPrf (synWne (synC1c) (synC0c)) :=
  by
  have p0000 := @gAddcid2 (synC1c)
  have p0001 := @gN0cnsuc (synC0c)
  have p0002 := @gEqnetrri (synCplc (synC0c) (synC1c)) (synC1c) (synC0c) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part059`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tcfnex`. -/
@[expose]
noncomputable def gTcfnex : Nominal.NPrf (.classMem (synCtcfn) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
  let t : Var := freshVar proofSupport 6
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_z_ne_p : z ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_z : p ≠ z := Ne.symm fresh_z_ne_p
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have fresh_p_ne_u : p ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_u_ne_p : u ≠ p := Ne.symm fresh_p_ne_u
  have fresh_p_ne_t : p ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_t_ne_p : t ≠ p := Ne.symm fresh_p_ne_t
  have fresh_q_ne_u : q ≠ u :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_u_ne_q : u ≠ q := Ne.symm fresh_q_ne_u
  have fresh_q_ne_t : q ≠ t :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_t_ne_q : t ≠ q := Ne.symm fresh_q_ne_t
  have fresh_u_ne_t : u ≠ t :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_t_ne_u : t ≠ u := Ne.symm fresh_u_ne_t
  have dv_cache_0001 : p ∉ ((synCop (.cv z) (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_z, fresh_p_ne_x, or_false, not_false_eq_true])
  have dv_cache_0002 :
    p ∉
      ((synCsymdif (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
                (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                  (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                (synCpw1 (synC1c))))) (synCins3 (synCid)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.classMem (.cv p) (synCncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : t ∉ ((synCsn (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_q,
          not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_u, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((synCpw1fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((synWbr (.cv u) (synCsset) (.cv p))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_u, fresh_t_ne_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((synCsn (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_t,
          not_false_eq_true])
  have dv_cache_0009 :
    u ∉
      ((synWa (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))
          (synWbr (synCsn (.cv t)) (synCsset) (.cv p)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_ne_t, fresh_u_ne_p,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((synCsn (synCsn (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_q,
          not_false_eq_true])
  have dv_cache_0011 : u ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_p, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((synCsset)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((synCsi (synCpw1fn))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((synCpw1 (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_q,
          not_false_eq_true])
  have dv_cache_0015 : t ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_p, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((synCop (synCsn (synCsn (.cv q))) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_q, fresh_t_ne_x, or_false, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((synCtxp (synCsi (synCcnv (synCsset))) (synCsset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_q, not_false_eq_true])
  have dv_cache_0019 : t ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_x, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((synCop (.cv p) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_x, or_false, not_false_eq_true])
  have dv_cache_0021 :
    q ∉
      ((synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : z ∉ ((synCop (synCsn (.cv y)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0023 :
    z ∉
      ((synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                  (synCin (synCxp (synCncs) (synCvv)) (synCima
                      (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                          (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 : p ∉ ((synCuni (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_p_ne_x,
          not_false_eq_true])
  have dv_cache_0025 : q ∉ ((synCuni (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_x,
          not_false_eq_true])
  have dv_cache_0026 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0027 :
    z ∉
      ((synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
            (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_x,
          fresh_z_ne_q, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0028 : p ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show p ≠ z from (by exact fresh_p_ne_z))
  have dv_cache_0029 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0030 : x ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0031 :
    x ∉
      ((synCrn (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                    (synCin (synCxp (synCncs) (synCvv)) (synCima
                        (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn))) (synCima
                            (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                        (synCpw1 (synC1c))))) (synCins3 (synCid)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0032 :
    y ∉
      ((synCrn (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                    (synCin (synCxp (synCncs) (synCvv)) (synCima
                        (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn))) (synCima
                            (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                        (synCpw1 (synC1c))))) (synCins3 (synCid)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0033 : y ∉ ((synCtc (synCuni (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0034 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTcfn x
  have p0001 :=
    @gOteltxp (.cv z) (synCsn (.cv y)) (.cv x) (synCcnv (synCsset))
      (synCcompl (synCrn (synCsymdif (synCins2 (synCin (synCxp (synCncs) (synCvv))
                (synCima (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                    (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                      (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))
  have p0002 :=
    (Nominal.biimpRefl (synWbr (.cv z) (synCcnv (synCsset)) (synCsn (.cv y))))
  have p0003 := @gBrcnv (.cv z) (synCsn (.cv y)) (synCsset)
  have p0004 := @gVex y
  have p0005 := @gVex z
  have p0006 := @gBrssetsn (.cv y) (.cv z) p0004 p0005
  have p0007_e01_recanon :
    Nominal.NPrf (synWb (synWbr (synCsn (.cv y)) (synCsset) (.cv z)) (.objMem y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gBitri (synWbr (.cv z) (synCcnv (synCsset)) (synCsn (.cv y)))
      (synWbr (synCsn (.cv y)) (synCsset) (.cv z)) (.objMem y z) p0003
      p0007_e01_recanon
  have p0008 :=
    @gBitr3i (.classMem (synCop (.cv z) (synCsn (.cv y))) (synCcnv (synCsset)))
      (synWbr (.cv z) (synCcnv (synCsset)) (synCsn (.cv y))) (.objMem y z) p0002 p0007
  have p0009 := @gVex x
  have p0010 := @gOpex (.cv z) (.cv x) p0005 p0009
  have p0011 :=
    @gElcompl (synCop (.cv z) (.cv x))
      (synCrn (synCsymdif (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
                (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                  (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                (synCpw1 (synC1c))))) (synCins3 (synCid))))
      p0010
  have p0012 :=
    @gElrn2 p (synCop (.cv z) (.cv x))
      (synCsymdif (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
              (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
              (synCpw1 (synC1c))))) (synCins3 (synCid)))
      dv_cache_0001 dv_cache_0002
  have p0013 :=
    @gElsymdif (synCop (.cv p) (synCop (.cv z) (.cv x)))
      (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
            (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
              (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
            (synCpw1 (synC1c)))))
      (synCins3 (synCid))
  have p0014 :=
    @gOtelins2 (.cv p) (.cv z) (.cv x)
      (synCin (synCxp (synCncs) (synCvv)) (synCima
          (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c))))
      p0005
  have p0015 :=
    @gElin (synCop (.cv p) (.cv x)) (synCxp (synCncs) (synCvv))
      (synCima (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
        (synCpw1 (synC1c)))
  have p0016 := @gOpelxp (.cv p) (.cv x) (synCncs) (synCvv)
  have p0017 :=
    @gMpbiran2 (.classMem (synCop (.cv p) (.cv x)) (synCxp (synCncs) (synCvv)))
      (.classMem (.cv p) (synCncs)) (.classMem (.cv x) (synCvv)) p0009 p0016
  have p0018 :=
    @gAnbi1i (.classMem (synCop (.cv p) (.cv x)) (synCxp (synCncs) (synCvv)))
      (.classMem (.cv p) (synCncs))
      (.classMem (synCop (.cv p) (.cv x)) (synCima
          (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c))))
      p0017
  have p0019 := @gNcseqnc (.cv p) (synCpw1 (.cv q))
  have p0020 :=
    @gRexbidv (.classMem (.cv p) (synCncs))
      (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))
      (.classMem (synCpw1 (.cv q)) (.cv p)) q (synCuni (.cv x)) dv_cache_0003 p0019
  have p0021 :=
    @gOteltxp (synCsn (synCsn (.cv q))) (.cv p) (.cv x)
      (synCcom (synCsset) (synCsi (synCpw1fn)))
      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))
  have p0022 := @gSnex (.cv q)
  have p0023 :=
    @gBrsnsi1 t (synCsn (.cv q)) (.cv u) (synCpw1fn) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0022
  have p0024 :=
    @gAnbi1i (synWbr (synCsn (synCsn (.cv q))) (synCsi (synCpw1fn)) (.cv u))
      (synWex t (synWa (.classEq (.cv u) (synCsn (.cv t)))
          (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))))
      (synWbr (.cv u) (synCsset) (.cv p)) p0023
  have p0025 :=
    @gN1941v
      (synWa (.classEq (.cv u) (synCsn (.cv t)))
        (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
      (synWbr (.cv u) (synCsset) (.cv p)) t dv_cache_0007
  have p0026 :=
    @gBitr4i
      (synWa (synWbr (synCsn (synCsn (.cv q))) (synCsi (synCpw1fn)) (.cv u))
        (synWbr (.cv u) (synCsset) (.cv p)))
      (synWa (synWex t (synWa (.classEq (.cv u) (synCsn (.cv t)))
            (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))))
        (synWbr (.cv u) (synCsset) (.cv p)))
      (synWex t (synWa (synWa (.classEq (.cv u) (synCsn (.cv t)))
            (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
          (synWbr (.cv u) (synCsset) (.cv p))))
      p0024 p0025
  have p0027 :=
    @gExbii
      (synWa (synWbr (synCsn (synCsn (.cv q))) (synCsi (synCpw1fn)) (.cv u))
        (synWbr (.cv u) (synCsset) (.cv p)))
      (synWex t (synWa (synWa (.classEq (.cv u) (synCsn (.cv t)))
            (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
          (synWbr (.cv u) (synCsset) (.cv p))))
      u p0026
  have p0028 :=
    @gExcom
      (synWa (synWa (.classEq (.cv u) (synCsn (.cv t)))
          (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
        (synWbr (.cv u) (synCsset) (.cv p)))
      u t
  have p0029 :=
    @gAnass (.classEq (.cv u) (synCsn (.cv t)))
      (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))
      (synWbr (.cv u) (synCsset) (.cv p))
  have p0030 :=
    @gExbii
      (synWa (synWa (.classEq (.cv u) (synCsn (.cv t)))
          (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
        (synWbr (.cv u) (synCsset) (.cv p)))
      (synWa (.classEq (.cv u) (synCsn (.cv t)))
        (synWa (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))
          (synWbr (.cv u) (synCsset) (.cv p))))
      u p0029
  have p0031 := @gSnex (.cv t)
  have p0032 := @gBreq1 (.cv u) (synCsn (.cv t)) (.cv p) (synCsset)
  have p0033 :=
    @gAnbi2d (.classEq (.cv u) (synCsn (.cv t))) (synWbr (.cv u) (synCsset) (.cv p))
      (synWbr (synCsn (.cv t)) (synCsset) (.cv p))
      (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)) p0032
  have p0034 :=
    @gCeqsexv
      (synWa (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))
        (synWbr (.cv u) (synCsset) (.cv p)))
      (synWa (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))
        (synWbr (synCsn (.cv t)) (synCsset) (.cv p)))
      u (synCsn (.cv t)) dv_cache_0008 dv_cache_0009 p0031 p0033
  have p0035 := @gVex q
  have p0036 := @gBrpw1fn (.cv q) (.cv t) p0035
  have p0037 := @gVex t
  have p0038 := @gVex p
  have p0039 := @gBrssetsn (.cv t) (.cv p) p0037 p0038
  have p0040_e01_recanon :
    Nominal.NPrf (synWb (synWbr (synCsn (.cv t)) (synCsset) (.cv p)) (.objMem t p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0039
  have p0040 :=
    @gAnbi12i (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))
      (.classEq (.cv t) (synCpw1 (.cv q)))
      (synWbr (synCsn (.cv t)) (synCsset) (.cv p)) (.objMem t p) p0036
      p0040_e01_recanon
  have p0041 :=
    @gN3bitri
      (synWex u (synWa (synWa (.classEq (.cv u) (synCsn (.cv t)))
            (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
          (synWbr (.cv u) (synCsset) (.cv p))))
      (synWex u (synWa (.classEq (.cv u) (synCsn (.cv t)))
          (synWa (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))
            (synWbr (.cv u) (synCsset) (.cv p)))))
      (synWa (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t))
        (synWbr (synCsn (.cv t)) (synCsset) (.cv p)))
      (synWa (.classEq (.cv t) (synCpw1 (.cv q))) (.objMem t p)) p0030 p0034 p0040
  have p0042 :=
    @gExbii
      (synWex u (synWa (synWa (.classEq (.cv u) (synCsn (.cv t)))
            (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
          (synWbr (.cv u) (synCsset) (.cv p))))
      (synWa (.classEq (.cv t) (synCpw1 (.cv q))) (.objMem t p)) t p0041
  have p0043 :=
    @gN3bitri
      (synWex u (synWa (synWbr (synCsn (synCsn (.cv q))) (synCsi (synCpw1fn)) (.cv u))
          (synWbr (.cv u) (synCsset) (.cv p))))
      (synWex u (synWex t (synWa (synWa (.classEq (.cv u) (synCsn (.cv t)))
              (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
            (synWbr (.cv u) (synCsset) (.cv p)))))
      (synWex t (synWex u (synWa (synWa (.classEq (.cv u) (synCsn (.cv t)))
              (synWbr (synCsn (.cv q)) (synCpw1fn) (.cv t)))
            (synWbr (.cv u) (synCsset) (.cv p)))))
      (synWex t (synWa (.classEq (.cv t) (synCpw1 (.cv q))) (.objMem t p))) p0027 p0028
      p0042
  have p0044 :=
    @gOpelco u (synCsn (synCsn (.cv q))) (.cv p) (synCsset) (synCsi (synCpw1fn))
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0045 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t
      (synCpw1 (.cv q)) (.cv p) dv_cache_0014 dv_cache_0015)
  have p0046_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCpw1 (.cv q)) (.cv p))
        (synWex t (synWa (.classEq (.cv t) (synCpw1 (.cv q))) (.objMem t p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCpw1 synCin synCcompl synCnin synWnan synWa synCpw synWss
          synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0045
  have p0046 :=
    @gN3bitr4i
      (synWex u (synWa (synWbr (synCsn (synCsn (.cv q))) (synCsi (synCpw1fn)) (.cv u))
          (synWbr (.cv u) (synCsset) (.cv p))))
      (synWex t (synWa (.classEq (.cv t) (synCpw1 (.cv q))) (.objMem t p)))
      (.classMem (synCop (synCsn (synCsn (.cv q))) (.cv p))
        (synCcom (synCsset) (synCsi (synCpw1fn))))
      (.classMem (synCpw1 (.cv q)) (.cv p)) p0043 p0044 p0046_e02_recanon
  have p0047 :=
    @gOteltxp (synCsn (.cv t)) (synCsn (synCsn (.cv q))) (.cv x)
      (synCsi (synCcnv (synCsset))) (synCsset)
  have p0048 :=
    (Nominal.biimpRefl (synWbr (synCsn (.cv t)) (synCsi (synCcnv (synCsset)))
        (synCsn (synCsn (.cv q)))))
  have p0049 := @gBrsnsi (.cv t) (synCsn (.cv q)) (synCcnv (synCsset)) p0037 p0022
  have p0050 := @gBrcnv (.cv t) (synCsn (.cv q)) (synCsset)
  have p0051 := @gBrssetsn (.cv q) (.cv t) p0035 p0037
  have p0052_e02_recanon :
    Nominal.NPrf (synWb (synWbr (synCsn (.cv q)) (synCsset) (.cv t)) (.objMem q t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0051
  have p0052 :=
    @gN3bitri
      (synWbr (synCsn (.cv t)) (synCsi (synCcnv (synCsset))) (synCsn (synCsn (.cv q))))
      (synWbr (.cv t) (synCcnv (synCsset)) (synCsn (.cv q)))
      (synWbr (synCsn (.cv q)) (synCsset) (.cv t)) (.objMem q t) p0049 p0050
      p0052_e02_recanon
  have p0053 :=
    @gBitr3i
      (.classMem (synCop (synCsn (.cv t)) (synCsn (synCsn (.cv q))))
        (synCsi (synCcnv (synCsset))))
      (synWbr (synCsn (.cv t)) (synCsi (synCcnv (synCsset))) (synCsn (synCsn (.cv q))))
      (.objMem q t) p0048 p0052
  have p0054 := @gOpelssetsn (.cv t) (.cv x) p0037 p0009
  have p0055_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv t)) (.cv x)) (synCsset)) (.objMem t x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0054
  have p0055 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv t)) (synCsn (synCsn (.cv q))))
        (synCsi (synCcnv (synCsset))))
      (.objMem q t) (.classMem (synCop (synCsn (.cv t)) (.cv x)) (synCsset))
      (.objMem t x) p0053 p0055_e01_recanon
  have p0056 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (synCsn (.cv q))) (.cv x)))
        (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)))
      (synWa (.classMem (synCop (synCsn (.cv t)) (synCsn (synCsn (.cv q))))
          (synCsi (synCcnv (synCsset))))
        (.classMem (synCop (synCsn (.cv t)) (.cv x)) (synCsset)))
      (synWa (.objMem q t) (.objMem t x)) p0047 p0055
  have p0057 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (synCsn (.cv q))) (.cv x)))
        (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)))
      (synWa (.objMem q t) (.objMem t x)) t p0056
  have p0058 :=
    @gElima1c t (synCop (synCsn (synCsn (.cv q))) (.cv x))
      (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) dv_cache_0016 dv_cache_0017
  have p0059 := @gEluni t (.cv q) (.cv x) dv_cache_0018 dv_cache_0019
  have p0060_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv q) (synCuni (.cv x)))
        (synWex t (synWa (.objMem q t) (.objMem t x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0059
  have p0060 :=
    @gN3bitr4i
      (synWex t (.classMem
          (synCop (synCsn (.cv t)) (synCop (synCsn (synCsn (.cv q))) (.cv x)))
          (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))))
      (synWex t (synWa (.objMem q t) (.objMem t x)))
      (.classMem (synCop (synCsn (synCsn (.cv q))) (.cv x))
        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
      (.classMem (.cv q) (synCuni (.cv x))) p0057 p0058 p0060_e02_recanon
  have p0061 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (synCsn (.cv q))) (.cv p))
        (synCcom (synCsset) (synCsi (synCpw1fn))))
      (.classMem (synCpw1 (.cv q)) (.cv p))
      (.classMem (synCop (synCsn (synCsn (.cv q))) (.cv x))
        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
      (.classMem (.cv q) (synCuni (.cv x))) p0046 p0060
  have p0062 :=
    @gAncom (.classMem (synCpw1 (.cv q)) (.cv p)) (.classMem (.cv q) (synCuni (.cv x)))
  have p0063 :=
    @gN3bitri
      (.classMem (synCop (synCsn (synCsn (.cv q))) (synCop (.cv p) (.cv x)))
        (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))))
      (synWa (.classMem (synCop (synCsn (synCsn (.cv q))) (.cv p))
          (synCcom (synCsset) (synCsi (synCpw1fn))))
        (.classMem (synCop (synCsn (synCsn (.cv q))) (.cv x))
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))))
      (synWa (.classMem (synCpw1 (.cv q)) (.cv p)) (.classMem (.cv q) (synCuni (.cv x))))
      (synWa (.classMem (.cv q) (synCuni (.cv x))) (.classMem (synCpw1 (.cv q)) (.cv p)))
      p0021 p0061 p0062
  have p0064 :=
    @gExbii
      (.classMem (synCop (synCsn (synCsn (.cv q))) (synCop (.cv p) (.cv x)))
        (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))))
      (synWa (.classMem (.cv q) (synCuni (.cv x))) (.classMem (synCpw1 (.cv q)) (.cv p)))
      q p0063
  have p0065 :=
    @gElimapw11c q (synCop (.cv p) (.cv x))
      (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
      dv_cache_0020 dv_cache_0021
  have p0066 :=
    (Nominal.biimpRefl (synWrex q (synCuni (.cv x)) (.classMem (synCpw1 (.cv q)) (.cv p))))
  have p0067 :=
    @gN3bitr4i
      (synWex q (.classMem (synCop (synCsn (synCsn (.cv q))) (synCop (.cv p) (.cv x)))
          (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))))
      (synWex q (synWa (.classMem (.cv q) (synCuni (.cv x)))
          (.classMem (synCpw1 (.cv q)) (.cv p))))
      (.classMem (synCop (.cv p) (.cv x)) (synCima
          (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c))))
      (synWrex q (synCuni (.cv x)) (.classMem (synCpw1 (.cv q)) (.cv p))) p0064 p0065
      p0066
  have p0068 :=
    @gSyl6rbbr (.classMem (.cv p) (synCncs))
      (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))
      (synWrex q (synCuni (.cv x)) (.classMem (synCpw1 (.cv q)) (.cv p)))
      (.classMem (synCop (.cv p) (.cv x)) (synCima
          (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c))))
      p0020 p0067
  have p0069 :=
    @gPm532i (.classMem (.cv p) (synCncs))
      (.classMem (synCop (.cv p) (.cv x)) (synCima
          (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c))))
      (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))
      p0068
  have p0070 :=
    @gBitri
      (synWa (.classMem (synCop (.cv p) (.cv x)) (synCxp (synCncs) (synCvv)))
        (.classMem (synCop (.cv p) (.cv x)) (synCima
            (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
              (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
            (synCpw1 (synC1c)))))
      (synWa (.classMem (.cv p) (synCncs)) (.classMem (synCop (.cv p) (.cv x)) (synCima
            (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
              (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
            (synCpw1 (synC1c)))))
      (synWa (.classMem (.cv p) (synCncs))
        (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
      p0018 p0069
  have p0071 :=
    @gN3bitri
      (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCins2
          (synCin (synCxp (synCncs) (synCvv)) (synCima
              (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
              (synCpw1 (synC1c))))))
      (.classMem (synCop (.cv p) (.cv x)) (synCin (synCxp (synCncs) (synCvv)) (synCima
            (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
              (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
            (synCpw1 (synC1c)))))
      (synWa (.classMem (synCop (.cv p) (.cv x)) (synCxp (synCncs) (synCvv)))
        (.classMem (synCop (.cv p) (.cv x)) (synCima
            (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
              (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
            (synCpw1 (synC1c)))))
      (synWa (.classMem (.cv p) (synCncs))
        (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
      p0014 p0015 p0070
  have p0072 := @gOtelins3 (.cv p) (.cv z) (.cv x) (synCid) p0009
  have p0073 := (Nominal.biimpRefl (synWbr (.cv p) (synCid) (.cv z)))
  have p0074 := @gIdeq (.cv p) (.cv z) p0005
  have p0075_e01_recanon :
    Nominal.NPrf (synWb (synWbr (.cv p) (synCid) (.cv z)) (.objEq p z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0074
  have p0075 :=
    @gBitr3i (.classMem (synCop (.cv p) (.cv z)) (synCid))
      (synWbr (.cv p) (synCid) (.cv z)) (.objEq p z) p0073 p0075_e01_recanon
  have p0076 :=
    @gBitri (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCins3 (synCid)))
      (.classMem (synCop (.cv p) (.cv z)) (synCid)) (.objEq p z) p0072 p0075
  have p0077 :=
    @gBibi12i
      (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCins2
          (synCin (synCxp (synCncs) (synCvv)) (synCima
              (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
              (synCpw1 (synC1c))))))
      (synWa (.classMem (.cv p) (synCncs))
        (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
      (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCins3 (synCid)))
      (.objEq p z) p0071 p0076
  have p0078 :=
    @gXchbinx
      (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCsymdif (synCins2
            (synCin (synCxp (synCncs) (synCvv)) (synCima
                (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                  (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                (synCpw1 (synC1c))))) (synCins3 (synCid))))
      (synWb (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCins2
            (synCin (synCxp (synCncs) (synCvv)) (synCima
                (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                  (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                (synCpw1 (synC1c))))))
        (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCins3 (synCid))))
      (synWb (synWa (.classMem (.cv p) (synCncs))
          (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
        (.objEq p z))
      p0013 p0077
  have p0079 :=
    @gExbii
      (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCsymdif (synCins2
            (synCin (synCxp (synCncs) (synCvv)) (synCima
                (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                  (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                (synCpw1 (synC1c))))) (synCins3 (synCid))))
      (.neg (synWb (synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
              (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))) (.objEq p z)))
      p p0078
  have p0080 :=
    @gExnal
      (synWb (synWa (.classMem (.cv p) (synCncs))
          (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
        (.objEq p z))
      p
  have p0081 :=
    @gN3bitrri
      (.classMem (synCop (.cv z) (.cv x)) (synCrn (synCsymdif (synCins2
              (synCin (synCxp (synCncs) (synCvv)) (synCima
                  (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                    (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                      (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))
      (synWex p (.classMem (synCop (.cv p) (synCop (.cv z) (.cv x))) (synCsymdif (synCins2
              (synCin (synCxp (synCncs) (synCvv)) (synCima
                  (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                    (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                      (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))
      (synWex p (.neg (synWb (synWa (.classMem (.cv p) (synCncs))
              (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
            (.objEq p z))))
      (.neg (.all p (synWb (synWa (.classMem (.cv p) (synCncs))
              (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
            (.objEq p z))))
      p0012 p0079 p0080
  have p0082 :=
    @gCon1bii
      (.all p (synWb (synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
              (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))) (.objEq p z)))
      (.classMem (synCop (.cv z) (.cv x)) (synCrn (synCsymdif (synCins2
              (synCin (synCxp (synCncs) (synCvv)) (synCima
                  (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                    (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                      (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))
      p0081
  have p0083 :=
    @gBitri
      (.classMem (synCop (.cv z) (.cv x)) (synCcompl (synCrn (synCsymdif (synCins2
                (synCin (synCxp (synCncs) (synCvv)) (synCima
                    (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                        (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid))))))
      (.neg (.classMem (synCop (.cv z) (.cv x)) (synCrn (synCsymdif (synCins2
                (synCin (synCxp (synCncs) (synCvv)) (synCima
                    (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                        (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid))))))
      (.all p (synWb (synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
              (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))) (.objEq p z)))
      p0011 p0082
  have p0084 :=
    @gAnbi12i (.classMem (synCop (.cv z) (synCsn (.cv y))) (synCcnv (synCsset)))
      (.objMem y z)
      (.classMem (synCop (.cv z) (.cv x)) (synCcompl (synCrn (synCsymdif (synCins2
                (synCin (synCxp (synCncs) (synCvv)) (synCima
                    (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                        (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid))))))
      (.all p (synWb (synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
              (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))) (.objEq p z)))
      p0008 p0083
  have p0085 :=
    @gBitri
      (.classMem (synCop (.cv z) (synCop (synCsn (.cv y)) (.cv x)))
        (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                  (synCin (synCxp (synCncs) (synCvv)) (synCima
                      (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                          (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))))
      (synWa (.classMem (synCop (.cv z) (synCsn (.cv y))) (synCcnv (synCsset)))
        (.classMem (synCop (.cv z) (.cv x)) (synCcompl (synCrn (synCsymdif (synCins2
                  (synCin (synCxp (synCncs) (synCvv)) (synCima
                      (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                          (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))))
      (synWa (.objMem y z) (.all p (synWb (synWa (.classMem (.cv p) (synCncs))
              (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
            (.objEq p z))))
      p0001 p0084
  have p0086 :=
    @gExbii
      (.classMem (synCop (.cv z) (synCop (synCsn (.cv y)) (.cv x)))
        (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                  (synCin (synCxp (synCncs) (synCvv)) (synCima
                      (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                          (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))))
      (synWa (.objMem y z) (.all p (synWb (synWa (.classMem (.cv p) (synCncs))
              (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
            (.objEq p z))))
      z p0085
  have p0087 :=
    @gElrn2 z (synCop (synCsn (.cv y)) (.cv x))
      (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                (synCin (synCxp (synCncs) (synCvv)) (synCima
                    (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                        (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid))))))
      dv_cache_0022 dv_cache_0023
  have p0088 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTc q
      (synCuni (.cv x)) p dv_cache_0024 dv_cache_0025 dv_cache_0026
  have p0089 :=
    @gDfiota2
      (synWa (.classMem (.cv p) (synCncs))
        (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
      p z dv_cache_0027 dv_cache_0028
  have p0090 :=
    @gEqtri (synCtc (synCuni (.cv x)))
      (synCio p (synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
            (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))))
      (synCuni (.cab z (.all p (synWb (synWa (.classMem (.cv p) (synCncs))
                (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
              (.objEq p z)))))
      p0088 p0089
  have p0091 :=
    @gEleq2i (synCtc (synCuni (.cv x)))
      (synCuni (.cab z (.all p (synWb (synWa (.classMem (.cv p) (synCncs))
                (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
              (.objEq p z)))))
      (.cv y) p0090
  have p0092 :=
    @gEluniab
      (.all p (synWb (synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
              (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))) (.objEq p z)))
      z (.cv y) dv_cache_0029
  have p0093_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv y) (synCuni (.cab z (.all p (synWb
                  (synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
                      (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))) (.objEq p z))))))
        (synWex z (synWa (.objMem y z) (.all p (synWb (synWa (.classMem (.cv p) (synCncs))
                  (synWrex q (synCuni (.cv x))
                    (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))) (.objEq p z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0092
  have p0093 :=
    @gBitri (.classMem (.cv y) (synCtc (synCuni (.cv x))))
      (.classMem (.cv y) (synCuni (.cab z (.all p (synWb
                (synWa (.classMem (.cv p) (synCncs)) (synWrex q (synCuni (.cv x))
                    (.classEq (.cv p) (synCnc (synCpw1 (.cv q)))))) (.objEq p z))))))
      (synWex z (synWa (.objMem y z) (.all p (synWb (synWa (.classMem (.cv p) (synCncs))
                (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
              (.objEq p z)))))
      p0091 p0093_e01_recanon
  have p0094 :=
    @gN3bitr4i
      (synWex z (.classMem (synCop (.cv z) (synCop (synCsn (.cv y)) (.cv x)))
          (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                    (synCin (synCxp (synCncs) (synCvv)) (synCima
                        (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn))) (synCima
                            (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                        (synCpw1 (synC1c))))) (synCins3 (synCid))))))))
      (synWex z (synWa (.objMem y z) (.all p (synWb (synWa (.classMem (.cv p) (synCncs))
                (synWrex q (synCuni (.cv x)) (.classEq (.cv p) (synCnc (synCpw1 (.cv q))))))
              (.objEq p z)))))
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCrn (synCtxp (synCcnv (synCsset))
            (synCcompl (synCrn (synCsymdif (synCins2 (synCin (synCxp (synCncs) (synCvv))
                      (synCima (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                            (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid))))))))
      (.classMem (.cv y) (synCtc (synCuni (.cv x)))) p0086 p0087 p0093
  have p0095 :=
    @gReleqmpt x y (synC1c)
      (synCrn (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                  (synCin (synCxp (synCncs) (synCvv)) (synCima
                      (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                          (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))))
      (synCtc (synCuni (.cv x))) dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 p0094
  have p0096 :=
    @gEqtr4i (synCtcfn) (synCmpt x (synC1c) (synCtc (synCuni (.cv x))))
      (synCin (synCxp (synC1c) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCrn
                    (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif
                            (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
                                  (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                                    (synCima (synCtxp (synCsi (synCcnv (synCsset)))
                                        (synCsset)) (synC1c))) (synCpw1 (synC1c)))))
                            (synCins3 (synCid))))))))) (synC1c)))))
      p0000 p0095
  have p0097 := @gN1cex
  have p0098 := @gSsetex
  have p0099 := @gCnvex (synCsset) p0098
  have p0100 := @gNcsex
  have p0101 := @gVvex
  have p0102 := @gXpex (synCncs) (synCvv) p0100 p0101
  have p0104 := @gPw1fnex
  have p0105 := @gSiex (synCpw1fn) p0104
  have p0106 := @gCoex (synCsset) (synCsi (synCpw1fn)) p0098 p0105
  have p0107 := @gSiex (synCcnv (synCsset)) p0099
  have p0109 := @gTxpex (synCsi (synCcnv (synCsset))) (synCsset) p0107 p0098
  have p0111 :=
    @gImaex (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c) p0109 p0097
  have p0112 :=
    @gTxpex (synCcom (synCsset) (synCsi (synCpw1fn)))
      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)) p0106
      p0111
  have p0114 := @gPw1ex (synC1c) p0097
  have p0115 :=
    @gImaex
      (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
      (synCpw1 (synC1c)) p0112 p0114
  have p0116 :=
    @gInex (synCxp (synCncs) (synCvv))
      (synCima (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
        (synCpw1 (synC1c)))
      p0102 p0115
  have p0117 :=
    @gIns2ex
      (synCin (synCxp (synCncs) (synCvv)) (synCima
          (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c))))
      p0116
  have p0118 := @gIdex
  have p0119 := @gIns3ex (synCid) p0118
  have p0120 :=
    @gSymdifex
      (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
            (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
              (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
            (synCpw1 (synC1c)))))
      (synCins3 (synCid)) p0117 p0119
  have p0121 :=
    @gRnex
      (synCsymdif (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
              (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
              (synCpw1 (synC1c))))) (synCins3 (synCid)))
      p0120
  have p0122 :=
    @gComplex
      (synCrn (synCsymdif (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
                (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                  (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
                (synCpw1 (synC1c))))) (synCins3 (synCid))))
      p0121
  have p0123 :=
    @gTxpex (synCcnv (synCsset))
      (synCcompl (synCrn (synCsymdif (synCins2 (synCin (synCxp (synCncs) (synCvv))
                (synCima (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                    (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                      (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))
      p0099 p0122
  have p0124 :=
    @gRnex
      (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                (synCin (synCxp (synCncs) (synCvv)) (synCima
                    (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                        (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid))))))
      p0123
  have p0125 :=
    @gMptexlem (synC1c)
      (synCrn (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif (synCins2
                  (synCin (synCxp (synCncs) (synCvv)) (synCima
                      (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                          (synC1c))) (synCpw1 (synC1c))))) (synCins3 (synCid)))))))
      p0097 p0124
  have p0126 :=
    @gEqeltri (synCtcfn)
      (synCin (synCxp (synC1c) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCrn
                    (synCtxp (synCcnv (synCsset)) (synCcompl (synCrn (synCsymdif
                            (synCins2 (synCin (synCxp (synCncs) (synCvv)) (synCima
                                  (synCtxp (synCcom (synCsset) (synCsi (synCpw1fn)))
                                    (synCima (synCtxp (synCsi (synCcnv (synCsset)))
                                        (synCsset)) (synC1c))) (synCpw1 (synC1c)))))
                            (synCins3 (synCid))))))))) (synC1c)))))
      (synCvv) p0096 p0125
  exact p0126


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part060`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fntcfn`. -/
@[expose]
noncomputable def gFntcfn : Nominal.NPrf (synWfn (synCtcfn) (synC1c)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((synC1c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTcfn x
  have p0001 :=
    @gFnmpt x (synC1c) (synCtc (synCuni (.cv x))) (synCtcfn) (synCvv) dv_cache_0001
      p0000
  have p0002 := @gTcex (synCuni (.cv x))
  have p0003 :=
    @gA1i (.classMem (synCtc (synCuni (.cv x))) (synCvv))
      (.classMem (.cv x) (synC1c)) p0002
  have p0004 :=
    @gMprg (.classMem (synCtc (synCuni (.cv x))) (synCvv))
      (synWfn (synCtcfn) (synC1c)) x (synC1c) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_brtcfn`. -/
@[expose]
noncomputable def gBrtcfn (A : Class) (B : Class)
    (hyp_brtcfn_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (synWbr (synCsn A) (synCtcfn) B) (.classEq B (synCtc A))) :=
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
  have dv_cache_0001 : x ∉ ((synCsn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCtc A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gSnel1c A hyp_brtcfn_1
  have p0001 := @gUnieq (.cv x) (synCsn A)
  have p0002 := @gUnisn A hyp_brtcfn_1
  have p0003 :=
    @gSyl6eq (.classEq (.cv x) (synCsn A)) (synCuni (.cv x)) (synCuni (synCsn A)) A
      p0001 p0002
  have p0004 := @gTceq (synCuni (.cv x)) A
  have p0005 :=
    @gSyl (.classEq (.cv x) (synCsn A)) (.classEq (synCuni (.cv x)) A)
      (.classEq (synCtc (synCuni (.cv x))) (synCtc A)) p0003 p0004
  have p0006 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTcfn x
  have p0007 := @gTcex A
  have p0008 :=
    @gFvmpt x (synCsn A) (synCtc (synCuni (.cv x))) (synCtc A) (synC1c) (synCtcfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0005 p0006 p0007
  have p0009 := Nominal.mp p0000 p0008
  have p0010 := @gEqeq1i (synCfv (synCtcfn) (synCsn A)) (synCtc A) B p0009
  have p0011 := @gFntcfn
  have p0012 := @gFnbrfvb (synC1c) (synCsn A) B (synCtcfn)
  have p0013 :=
    @gMp2an (synWfn (synCtcfn) (synC1c)) (.classMem (synCsn A) (synC1c))
      (synWb (.classEq (synCfv (synCtcfn) (synCsn A)) B)
        (synWbr (synCsn A) (synCtcfn) B))
      p0011 p0000 p0012
  have p0014 := @gEqcom (synCtc A) B
  have p0015 :=
    @gN3bitr3i (.classEq (synCfv (synCtcfn) (synCsn A)) B) (.classEq (synCtc A) B)
      (synWbr (synCsn A) (synCtcfn) B) (.classEq B (synCtc A)) p0010 p0013 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_addcdi`. -/
@[expose]
noncomputable def gAddcdi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
        (.classEq (synCo A (synCmuc) (synCplc B C))
          (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((synCplc B C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          Finset.mem_union, fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0007 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0008 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((Wff.imp (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
            (synCplc (synCo A (synCmuc) (synCnc (.cv y)))
              (synCo A (synCmuc) (synCnc (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, fresh_x_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉
      ((Wff.classEq (synCo A (synCmuc) (synCplc B C))
          (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    z ∉
      ((Wff.classEq (synCo A (synCmuc) (synCplc B C))
          (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, fresh_z_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    y ∉
      ((synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_y_not_C, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_z_not_C, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 :
    x ∉
      ((Wff.classEq (synCo A (synCmuc) (synCplc B C))
          (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 :
    x ∉
      ((synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_x_not_C, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gNcaddccl B C
  have p0001 :=
    @gN3adant1 (.classMem B (synCncs)) (.classMem C (synCncs))
      (.classMem (synCplc B C) (synCncs)) (.classMem A (synCncs)) p0000
  have p0002 := @gElncs x (synCplc B C) dv_cache_0001
  have p0003 := @gVex x
  have p0004 := @gNcid (.cv x) p0003
  have p0005 := @gEleq2 (synCplc B C) (synCnc (.cv x)) (.cv x)
  have p0006 :=
    @gMpbiri (.classEq (synCplc B C) (synCnc (.cv x)))
      (.classMem (.cv x) (synCplc B C)) (.classMem (.cv x) (synCnc (.cv x))) p0004 p0005
  have p0007 :=
    @gEladdc (.cv x) B C y z dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0008 := @gNcseqnc B (.cv y)
  have p0009 := @gNcseqnc C (.cv z)
  have p0010 :=
    @gBi2anan9 (.classMem B (synCncs)) (.classEq B (synCnc (.cv y)))
      (.classMem (.cv y) B) (.classMem C (synCncs)) (.classEq C (synCnc (.cv z)))
      (.classMem (.cv z) C) p0008 p0009
  have p0011 :=
    @gN3adant1 (.classMem B (synCncs)) (.classMem C (synCncs))
      (synWb (synWa (.classEq B (synCnc (.cv y))) (.classEq C (synCnc (.cv z))))
        (synWa (.classMem (.cv y) B) (.classMem (.cv z) C)))
      (.classMem A (synCncs)) p0010
  have p0012 := @gElncs x A dv_cache_0009
  have p0013 := @gVex y
  have p0014 := @gVex z
  have p0015 := @gNcdisjun (.cv y) (.cv z) p0013 p0014
  have p0016 :=
    @gOveq2d (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (synCnc (synCun (.cv y) (.cv z))) (synCplc (synCnc (.cv y)) (synCnc (.cv z)))
      (synCnc (.cv x)) (synCmuc) p0015
  have p0017 := @gXpdisj2 (.cv y) (.cv z) (.cv x) (.cv x)
  have p0018 := @gXpex (.cv x) (.cv y) p0003 p0013
  have p0019 := @gXpex (.cv x) (.cv z) p0003 p0014
  have p0020 :=
    @gNcdisjun (synCxp (.cv x) (.cv y)) (synCxp (.cv x) (.cv z)) p0018 p0019
  have p0021 :=
    @gSyl (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (.classEq (synCin (synCxp (.cv x) (.cv y)) (synCxp (.cv x) (.cv z))) (synC0))
      (.classEq (synCnc (synCun (synCxp (.cv x) (.cv y)) (synCxp (.cv x) (.cv z))))
        (synCplc (synCnc (synCxp (.cv x) (.cv y))) (synCnc (synCxp (.cv x) (.cv z)))))
      p0017 p0020
  have p0022 := @gUnex (.cv y) (.cv z) p0013 p0014
  have p0023 := @gMucnc (.cv x) (synCun (.cv y) (.cv z)) p0003 p0022
  have p0024 := @gXpundi (.cv x) (.cv y) (.cv z)
  have p0025 :=
    @gNceqi (synCxp (.cv x) (synCun (.cv y) (.cv z)))
      (synCun (synCxp (.cv x) (.cv y)) (synCxp (.cv x) (.cv z))) p0024
  have p0026 :=
    @gEqtri (synCo (synCnc (.cv x)) (synCmuc) (synCnc (synCun (.cv y) (.cv z))))
      (synCnc (synCxp (.cv x) (synCun (.cv y) (.cv z))))
      (synCnc (synCun (synCxp (.cv x) (.cv y)) (synCxp (.cv x) (.cv z)))) p0023 p0025
  have p0027 := @gMucnc (.cv x) (.cv y) p0003 p0013
  have p0028 := @gMucnc (.cv x) (.cv z) p0003 p0014
  have p0029 :=
    @gAddceq12i (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
      (synCnc (synCxp (.cv x) (.cv y)))
      (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv z)))
      (synCnc (synCxp (.cv x) (.cv z))) p0027 p0028
  have p0030 :=
    @gN3eqtr4g (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (synCnc (synCun (synCxp (.cv x) (.cv y)) (synCxp (.cv x) (.cv z))))
      (synCplc (synCnc (synCxp (.cv x) (.cv y))) (synCnc (synCxp (.cv x) (.cv z))))
      (synCo (synCnc (.cv x)) (synCmuc) (synCnc (synCun (.cv y) (.cv z))))
      (synCplc (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
        (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv z))))
      p0021 p0026 p0029
  have p0031 :=
    @gEqtr3d (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (synCo (synCnc (.cv x)) (synCmuc) (synCnc (synCun (.cv y) (.cv z))))
      (synCo (synCnc (.cv x)) (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
      (synCplc (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
        (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv z))))
      p0016 p0030
  have p0032 :=
    @gOveq1 A (synCnc (.cv x)) (synCplc (synCnc (.cv y)) (synCnc (.cv z))) (synCmuc)
  have p0033 := @gOveq1 A (synCnc (.cv x)) (synCnc (.cv y)) (synCmuc)
  have p0034 := @gOveq1 A (synCnc (.cv x)) (synCnc (.cv z)) (synCmuc)
  have p0035 :=
    @gAddceq12d (.classEq A (synCnc (.cv x))) (synCo A (synCmuc) (synCnc (.cv y)))
      (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
      (synCo A (synCmuc) (synCnc (.cv z)))
      (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv z))) p0033 p0034
  have p0036 :=
    @gEqeq12d (.classEq A (synCnc (.cv x)))
      (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
      (synCo (synCnc (.cv x)) (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
      (synCplc (synCo A (synCmuc) (synCnc (.cv y))) (synCo A (synCmuc) (synCnc (.cv z))))
      (synCplc (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
        (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv z))))
      p0032 p0035
  have p0037 :=
    @gSyl5ibr (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (.classEq (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
        (synCplc (synCo A (synCmuc) (synCnc (.cv y)))
          (synCo A (synCmuc) (synCnc (.cv z)))))
      (.classEq A (synCnc (.cv x)))
      (.classEq (synCo (synCnc (.cv x)) (synCmuc)
          (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
        (synCplc (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
          (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv z)))))
      p0031 p0036
  have p0038 :=
    @gExlimiv (.classEq A (synCnc (.cv x)))
      (.imp (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
          (synCplc (synCo A (synCmuc) (synCnc (.cv y)))
            (synCo A (synCmuc) (synCnc (.cv z))))))
      x dv_cache_0010 p0037
  have p0039 :=
    @gSylbi (.classMem A (synCncs)) (synWex x (.classEq A (synCnc (.cv x))))
      (.imp (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
          (synCplc (synCo A (synCmuc) (synCnc (.cv y)))
            (synCo A (synCmuc) (synCnc (.cv z))))))
      p0012 p0038
  have p0040 :=
    @gAdantrd (.classMem A (synCncs)) (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (.classEq (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
        (synCplc (synCo A (synCmuc) (synCnc (.cv y)))
          (synCo A (synCmuc) (synCnc (.cv z)))))
      (.classEq (.cv x) (synCun (.cv y) (.cv z))) p0039
  have p0041 := @gAddceq12 B C (synCnc (.cv y)) (synCnc (.cv z))
  have p0042 :=
    @gOveq2d (synWa (.classEq B (synCnc (.cv y))) (.classEq C (synCnc (.cv z))))
      (synCplc B C) (synCplc (synCnc (.cv y)) (synCnc (.cv z))) A (synCmuc) p0041
  have p0043 := @gOveq2 B (synCnc (.cv y)) A (synCmuc)
  have p0044 :=
    @gAdantr (.classEq B (synCnc (.cv y)))
      (.classEq (synCo A (synCmuc) B) (synCo A (synCmuc) (synCnc (.cv y))))
      (.classEq C (synCnc (.cv z))) p0043
  have p0045 := @gOveq2 C (synCnc (.cv z)) A (synCmuc)
  have p0046 :=
    @gAdantl (.classEq C (synCnc (.cv z)))
      (.classEq (synCo A (synCmuc) C) (synCo A (synCmuc) (synCnc (.cv z))))
      (.classEq B (synCnc (.cv y))) p0045
  have p0047 :=
    @gAddceq12d (synWa (.classEq B (synCnc (.cv y))) (.classEq C (synCnc (.cv z))))
      (synCo A (synCmuc) B) (synCo A (synCmuc) (synCnc (.cv y)))
      (synCo A (synCmuc) C) (synCo A (synCmuc) (synCnc (.cv z))) p0044 p0046
  have p0048 :=
    @gEqeq12d (synWa (.classEq B (synCnc (.cv y))) (.classEq C (synCnc (.cv z))))
      (synCo A (synCmuc) (synCplc B C))
      (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
      (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C))
      (synCplc (synCo A (synCmuc) (synCnc (.cv y))) (synCo A (synCmuc) (synCnc (.cv z))))
      p0042 p0047
  have p0049 :=
    @gImbi2d (synWa (.classEq B (synCnc (.cv y))) (.classEq C (synCnc (.cv z))))
      (.classEq (synCo A (synCmuc) (synCplc B C))
        (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))
      (.classEq (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
        (synCplc (synCo A (synCmuc) (synCnc (.cv y)))
          (synCo A (synCmuc) (synCnc (.cv z)))))
      (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (.cv x) (synCun (.cv y) (.cv z))))
      p0048
  have p0050 :=
    @gSyl5ibrcom (.classMem A (synCncs))
      (.imp (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (.cv x) (synCun (.cv y) (.cv z))))
        (.classEq (synCo A (synCmuc) (synCplc B C))
          (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C))))
      (synWa (.classEq B (synCnc (.cv y))) (.classEq C (synCnc (.cv z))))
      (.imp (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (.cv x) (synCun (.cv y) (.cv z))))
        (.classEq (synCo A (synCmuc) (synCplc (synCnc (.cv y)) (synCnc (.cv z))))
          (synCplc (synCo A (synCmuc) (synCnc (.cv y)))
            (synCo A (synCmuc) (synCnc (.cv z))))))
      p0040 p0049
  have p0051 :=
    @gN3ad2ant1 (.classMem A (synCncs)) (.classMem B (synCncs))
      (.imp (synWa (.classEq B (synCnc (.cv y))) (.classEq C (synCnc (.cv z)))) (.imp
          (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
            (.classEq (.cv x) (synCun (.cv y) (.cv z))))
          (.classEq (synCo A (synCmuc) (synCplc B C))
            (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))))
      (.classMem C (synCncs)) p0050
  have p0052 :=
    @gSylbird
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synWa (.classMem (.cv y) B) (.classMem (.cv z) C))
      (synWa (.classEq B (synCnc (.cv y))) (.classEq C (synCnc (.cv z))))
      (.imp (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (.cv x) (synCun (.cv y) (.cv z))))
        (.classEq (synCo A (synCmuc) (synCplc B C))
          (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C))))
      p0011 p0051
  have p0053 :=
    @gRexlimdvv
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (.cv x) (synCun (.cv y) (.cv z))))
      (.classEq (synCo A (synCmuc) (synCplc B C))
        (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))
      y z B C dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0008 p0052
  have p0054 :=
    @gSyl5bi (.classMem (.cv x) (synCplc B C))
      (synWrex y B (synWrex z C (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
            (.classEq (.cv x) (synCun (.cv y) (.cv z))))))
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (.classEq (synCo A (synCmuc) (synCplc B C))
        (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))
      p0007 p0053
  have p0055 :=
    @gSyl5 (.classEq (synCplc B C) (synCnc (.cv x))) (.classMem (.cv x) (synCplc B C))
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (.classEq (synCo A (synCmuc) (synCplc B C))
        (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))
      p0006 p0054
  have p0056 :=
    @gExlimdv
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (.classEq (synCplc B C) (synCnc (.cv x)))
      (.classEq (synCo A (synCmuc) (synCplc B C))
        (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))
      x dv_cache_0015 dv_cache_0016 p0055
  have p0057 :=
    @gSyl5bi (.classMem (synCplc B C) (synCncs))
      (synWex x (.classEq (synCplc B C) (synCnc (.cv x))))
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (.classEq (synCo A (synCmuc) (synCplc B C))
        (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))
      p0002 p0056
  have p0058 :=
    @gMpd
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (.classMem (synCplc B C) (synCncs))
      (.classEq (synCo A (synCmuc) (synCplc B C))
        (synCplc (synCo A (synCmuc) B) (synCo A (synCmuc) C)))
      p0001 p0057
  exact p0058

/-- Checked nominal proof certificate identified upstream as `g_addcdir`. -/
@[expose]
noncomputable def gAddcdir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
        (.classEq (synCo (synCplc A B) (synCmuc) C)
          (synCplc (synCo A (synCmuc) C) (synCo B (synCmuc) C)))) :=
  by
  have p0000 := @gAddcdi C A B
  have p0001 :=
    @gN3coml (.classMem C (synCncs)) (.classMem A (synCncs)) (.classMem B (synCncs))
      (.classEq (synCo C (synCmuc) (synCplc A B))
        (synCplc (synCo C (synCmuc) A) (synCo C (synCmuc) B)))
      p0000
  have p0002 := @gNcaddccl A B
  have p0003 :=
    @gN3adant3 (.classMem A (synCncs)) (.classMem B (synCncs))
      (.classMem (synCplc A B) (synCncs)) (.classMem C (synCncs)) p0002
  have p0004 :=
    @gSimp3 (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs))
  have p0005 := @gMuccom (synCplc A B) C
  have p0006 :=
    @gSyl2anc
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (.classMem (synCplc A B) (synCncs)) (.classMem C (synCncs))
      (.classEq (synCo (synCplc A B) (synCmuc) C) (synCo C (synCmuc) (synCplc A B)))
      p0003 p0004 p0005
  have p0007 := @gMuccom A C
  have p0008 :=
    @gN3adant2 (.classMem A (synCncs)) (.classMem C (synCncs))
      (.classEq (synCo A (synCmuc) C) (synCo C (synCmuc) A)) (.classMem B (synCncs))
      p0007
  have p0009 := @gMuccom B C
  have p0010 :=
    @gN3adant1 (.classMem B (synCncs)) (.classMem C (synCncs))
      (.classEq (synCo B (synCmuc) C) (synCo C (synCmuc) B)) (.classMem A (synCncs))
      p0009
  have p0011 :=
    @gAddceq12d
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synCo A (synCmuc) C) (synCo C (synCmuc) A) (synCo B (synCmuc) C)
      (synCo C (synCmuc) B) p0008 p0010
  have p0012 :=
    @gN3eqtr4d
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synCo C (synCmuc) (synCplc A B))
      (synCplc (synCo C (synCmuc) A) (synCo C (synCmuc) B))
      (synCo (synCplc A B) (synCmuc) C)
      (synCplc (synCo A (synCmuc) C) (synCo B (synCmuc) C)) p0001 p0006 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_lemuc1`. -/
@[expose]
noncomputable def gLemuc1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
            (.classMem C (synCncs))) (synWbr A (synClec) B))
        (synWbr (synCo A (synCmuc) C) (synClec) (synCo B (synCmuc) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : q ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_B, not_false_eq_true])
  have dv_cache_0003 :
    q ∉ ((synWbr (synCo A (synCmuc) C) (synClec) (synCo B (synCmuc) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_C, fresh_q_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 :
    q ∉ ((synWa (.classMem A (synCncs)) (.classMem C (synCncs)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gDflec2 A B q dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gN3adant3 (.classMem A (synCncs)) (.classMem B (synCncs))
      (synWb (synWbr A (synClec) B)
        (synWrex q (synCncs) (.classEq B (synCplc A (.cv q)))))
      (.classMem C (synCncs)) p0000
  have p0002 := @gMuccl A C
  have p0003 :=
    @gAdantr (synWa (.classMem A (synCncs)) (.classMem C (synCncs)))
      (.classMem (synCo A (synCmuc) C) (synCncs)) (.classMem (.cv q) (synCncs)) p0002
  have p0004 := @gMuccl (.cv q) C
  have p0005 :=
    @gAncoms (.classMem (.cv q) (synCncs)) (.classMem C (synCncs))
      (.classMem (synCo (.cv q) (synCmuc) C) (synCncs)) p0004
  have p0006 :=
    @gAdantll (.classMem C (synCncs)) (.classMem (.cv q) (synCncs))
      (.classMem (synCo (.cv q) (synCmuc) C) (synCncs)) (.classMem A (synCncs)) p0005
  have p0007 := @gAddlecncs (synCo A (synCmuc) C) (synCo (.cv q) (synCmuc) C)
  have p0008 :=
    @gSyl2anc
      (synWa (synWa (.classMem A (synCncs)) (.classMem C (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (.classMem (synCo A (synCmuc) C) (synCncs))
      (.classMem (synCo (.cv q) (synCmuc) C) (synCncs))
      (synWbr (synCo A (synCmuc) C) (synClec)
        (synCplc (synCo A (synCmuc) C) (synCo (.cv q) (synCmuc) C)))
      p0003 p0006 p0007
  have p0009 :=
    @gSimpll (.classMem A (synCncs)) (.classMem C (synCncs))
      (.classMem (.cv q) (synCncs))
  have p0010 :=
    @gSimpr (synWa (.classMem A (synCncs)) (.classMem C (synCncs)))
      (.classMem (.cv q) (synCncs))
  have p0011 :=
    @gSimplr (.classMem A (synCncs)) (.classMem C (synCncs))
      (.classMem (.cv q) (synCncs))
  have p0012 := @gAddcdir A (.cv q) C
  have p0013 :=
    @gSyl3anc
      (synWa (synWa (.classMem A (synCncs)) (.classMem C (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (.classMem A (synCncs)) (.classMem (.cv q) (synCncs)) (.classMem C (synCncs))
      (.classEq (synCo (synCplc A (.cv q)) (synCmuc) C)
        (synCplc (synCo A (synCmuc) C) (synCo (.cv q) (synCmuc) C)))
      p0009 p0010 p0011 p0012
  have p0014 :=
    @gBreqtrrd
      (synWa (synWa (.classMem A (synCncs)) (.classMem C (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (synCo A (synCmuc) C)
      (synCplc (synCo A (synCmuc) C) (synCo (.cv q) (synCmuc) C))
      (synCo (synCplc A (.cv q)) (synCmuc) C) (synClec) p0008 p0013
  have p0015 := @gOveq1 B (synCplc A (.cv q)) C (synCmuc)
  have p0016 :=
    @gBreq2d (.classEq B (synCplc A (.cv q))) (synCo B (synCmuc) C)
      (synCo (synCplc A (.cv q)) (synCmuc) C) (synCo A (synCmuc) C) (synClec) p0015
  have p0017 :=
    @gSyl5ibrcom
      (synWa (synWa (.classMem A (synCncs)) (.classMem C (synCncs)))
        (.classMem (.cv q) (synCncs)))
      (synWbr (synCo A (synCmuc) C) (synClec) (synCo B (synCmuc) C))
      (.classEq B (synCplc A (.cv q)))
      (synWbr (synCo A (synCmuc) C) (synClec) (synCo (synCplc A (.cv q)) (synCmuc) C))
      p0014 p0016
  have p0018 :=
    @gRexlimdva (synWa (.classMem A (synCncs)) (.classMem C (synCncs)))
      (.classEq B (synCplc A (.cv q)))
      (synWbr (synCo A (synCmuc) C) (synClec) (synCo B (synCmuc) C)) q (synCncs)
      dv_cache_0003 dv_cache_0004 p0017
  have p0019 :=
    @gN3adant2 (.classMem A (synCncs)) (.classMem C (synCncs))
      (.imp (synWrex q (synCncs) (.classEq B (synCplc A (.cv q))))
        (synWbr (synCo A (synCmuc) C) (synClec) (synCo B (synCmuc) C)))
      (.classMem B (synCncs)) p0018
  have p0020 :=
    @gSylbid
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synWbr A (synClec) B) (synWrex q (synCncs) (.classEq B (synCplc A (.cv q))))
      (synWbr (synCo A (synCmuc) C) (synClec) (synCo B (synCmuc) C)) p0001 p0019
  have p0021 :=
    @gImp
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synWbr A (synClec) B)
      (synWbr (synCo A (synCmuc) C) (synClec) (synCo B (synCmuc) C)) p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_lemuc2`. -/
@[expose]
noncomputable def gLemuc2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
            (.classMem C (synCncs))) (synWbr B (synClec) C))
        (synWbr (synCo A (synCmuc) B) (synClec) (synCo A (synCmuc) C))) :=
  by
  have p0000 :=
    @gN3anrot (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs))
  have p0001 := @gLemuc1 B C A
  have p0002 :=
    @gSylanb
      (synW3a (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs)))
      (synW3a (.classMem B (synCncs)) (.classMem C (synCncs)) (.classMem A (synCncs)))
      (synWbr B (synClec) C)
      (synWbr (synCo B (synCmuc) A) (synClec) (synCo C (synCmuc) A)) p0000 p0001
  have p0003 :=
    @gSimpl1 (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs))
      (synWbr B (synClec) C)
  have p0004 :=
    @gSimpl2 (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs))
      (synWbr B (synClec) C)
  have p0005 := @gMuccom A B
  have p0006 :=
    @gSyl2anc
      (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs))) (synWbr B (synClec) C))
      (.classMem A (synCncs)) (.classMem B (synCncs))
      (.classEq (synCo A (synCmuc) B) (synCo B (synCmuc) A)) p0003 p0004 p0005
  have p0007 :=
    @gSimpl3 (.classMem A (synCncs)) (.classMem B (synCncs)) (.classMem C (synCncs))
      (synWbr B (synClec) C)
  have p0008 := @gMuccom A C
  have p0009 :=
    @gSyl2anc
      (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs))) (synWbr B (synClec) C))
      (.classMem A (synCncs)) (.classMem C (synCncs))
      (.classEq (synCo A (synCmuc) C) (synCo C (synCmuc) A)) p0003 p0007 p0008
  have p0010 :=
    @gN3brtr4d
      (synWa (synW3a (.classMem A (synCncs)) (.classMem B (synCncs))
          (.classMem C (synCncs))) (synWbr B (synClec) C))
      (synCo B (synCmuc) A) (synCo C (synCmuc) A) (synCo A (synCmuc) B)
      (synCo A (synCmuc) C) (synClec) p0002 p0006 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_n_0lt1c`. -/
@[expose]
noncomputable def gN0lt1c : Nominal.NPrf (synWbr (synC0c) (synCltc) (synC1c)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @gDf0c2
  have p0001 := @gN0ss (synCsn (.cv x))
  have p0002 := @gN0ex
  have p0003 := @gSnex (.cv x)
  have p0004 := @gNclec (synC0) (synCsn (.cv x)) p0002 p0003
  have p0005 := Nominal.mp p0001 p0004
  have p0006 :=
    @gEqbrtri (synC0c) (synCnc (synC0)) (synCnc (synCsn (.cv x))) (synClec) p0000
      p0005
  have p0007 := @gVex x
  have p0008 := @gSnnz (.cv x) p0007
  have p0009 := (Nominal.biimpRefl (synWne (synCsn (.cv x)) (synC0)))
  have p0010 :=
    @gMpbi (synWne (synCsn (.cv x)) (synC0))
      (.neg (.classEq (synCsn (.cv x)) (synC0))) p0008 p0009
  have p0011 := @gNcid (synCsn (.cv x)) p0003
  have p0012 := @gEleq2 (synC0c) (synCnc (synCsn (.cv x))) (synCsn (.cv x))
  have p0013 :=
    @gMpbiri (.classEq (synC0c) (synCnc (synCsn (.cv x))))
      (.classMem (synCsn (.cv x)) (synC0c))
      (.classMem (synCsn (.cv x)) (synCnc (synCsn (.cv x)))) p0011 p0012
  have p0014 := @gEl0c (synCsn (.cv x))
  have p0015 :=
    @gSylib (.classEq (synC0c) (synCnc (synCsn (.cv x))))
      (.classMem (synCsn (.cv x)) (synC0c)) (.classEq (synCsn (.cv x)) (synC0)) p0013
      p0014
  have p0016 :=
    @gMto (.classEq (synC0c) (synCnc (synCsn (.cv x))))
      (.classEq (synCsn (.cv x)) (synC0)) p0010 p0015
  have p0017 := (Nominal.biimpRefl (synWne (synC0c) (synCnc (synCsn (.cv x)))))
  have p0018 :=
    @gMpbir (synWne (synC0c) (synCnc (synCsn (.cv x))))
      (.neg (.classEq (synC0c) (synCnc (synCsn (.cv x))))) p0016 p0017
  have p0019 := @gBrltc (synC0c) (synCnc (synCsn (.cv x)))
  have p0020 :=
    @gMpbir2an (synWbr (synC0c) (synCltc) (synCnc (synCsn (.cv x))))
      (synWbr (synC0c) (synClec) (synCnc (synCsn (.cv x))))
      (synWne (synC0c) (synCnc (synCsn (.cv x)))) p0006 p0018 p0019
  have p0021 := @gDf1c3 (.cv x) p0007
  have p0022 :=
    @gBreqtrri (synC0c) (synCnc (synCsn (.cv x))) (synC1c) (synCltc) p0020 p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end
