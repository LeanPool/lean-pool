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

@[expose]
noncomputable def g_taddc (A : Class) (B : Class) (X : Class) (c : Var)
    (dv_X_c : c ∉ X.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
            (.classMem X (syn_cncs))) (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)))
        (syn_wrex c (syn_cncs) (.classEq X (syn_ctc (.cv c))))) :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq X (syn_cnc (.cv z)))).fv :=
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
  have dv_cache_0005 : y ∉ ((Wff.classEq X (syn_cnc (.cv z)))).fv :=
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
  have dv_cache_0006 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv :=
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
  have dv_cache_0007 : z ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv :=
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
  have dv_cache_0008 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv :=
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
  have dv_cache_0009 : z ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv :=
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
  have dv_cache_0012 : a ∉ ((syn_cpw1 (.cv x))).fv :=
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
  have dv_cache_0013 : b ∉ ((syn_cpw1 (.cv x))).fv :=
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
  have dv_cache_0014 : a ∉ ((syn_cnc (syn_cpw1 (.cv y)))).fv :=
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
  have dv_cache_0015 : b ∉ ((syn_cnc (syn_cpw1 (.cv y)))).fv :=
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
  have dv_cache_0016 : a ∉ ((syn_cnc (.cv z))).fv :=
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
  have dv_cache_0017 : b ∉ ((syn_cnc (.cv z))).fv :=
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
  have dv_cache_0026 : w ∉ ((Wff.classMem (.cv b) (syn_cnc (.cv z)))).fv :=
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
    c ∉ ((syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))).fv :=
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
  have dv_cache_0028 : c ∉ ((Wff.classMem (.cv b) (syn_cnc (.cv z)))).fv :=
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
    b ∉ ((syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))).fv :=
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
    a ∉ ((syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))).fv :=
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
  have dv_cache_0031 : w ∉ ((Wff.classEq X (syn_cnc (.cv z)))).fv :=
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
      ((Wff.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
          (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))).fv :=
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
      ((Wff.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
          (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))).fv :=
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
      ((Wff.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
          (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))).fv :=
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
  have dv_cache_0036 : w ∉ ((Wff.classEq X (syn_ctc (.cv c)))).fv :=
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
  have dv_cache_0037 : c ∉ ((syn_cnc (.cv w))).fv :=
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
  have dv_cache_0038 : c ∉ ((Wff.classEq X (syn_cnc (syn_cpw1 (.cv w))))).fv :=
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
  have p0000 := @g_elncs x A dv_cache_0001
  have p0001 := @g_elncs y B dv_cache_0002
  have p0002 := @g_elncs z X dv_cache_0003
  have p0003 :=
    @g_n_3anbi123i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))
      (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y))))
      (.classMem X (syn_cncs)) (syn_wex z (.classEq X (syn_cnc (.cv z)))) p0000 p0001
      p0002
  have p0004 :=
    @g_eeeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
      (.classEq X (syn_cnc (.cv z))) x y z dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0005 :=
    @g_bitr4i
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem X (syn_cncs)))
      (syn_w3a (syn_wex x (.classEq A (syn_cnc (.cv x))))
        (syn_wex y (.classEq B (syn_cnc (.cv y)))) (syn_wex z (.classEq X (syn_cnc (.cv z)))))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
              (.classEq X (syn_cnc (.cv z)))))))
      p0003 p0004
  have p0006 := @g_vex x
  have p0007 := @g_tcnc (.cv x) p0006
  have p0008 := @g_vex y
  have p0009 := @g_tcnc (.cv y) p0008
  have p0010 :=
    @g_addceq1i (syn_ctc (syn_cnc (.cv y))) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))
      p0009
  have p0011 :=
    @g_eqeq12i (syn_ctc (syn_cnc (.cv x))) (syn_cnc (syn_cpw1 (.cv x)))
      (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z)))
      (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))) p0007 p0010
  have p0012 :=
    @g_eqcom (syn_cnc (syn_cpw1 (.cv x)))
      (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)))
  have p0013 := @g_pw1ex (.cv y) p0008
  have p0014 := @g_ncelncsi (syn_cpw1 (.cv y)) p0013
  have p0015 := @g_vex z
  have p0016 := @g_ncelncsi (.cv z) p0015
  have p0017 := @g_ncaddccl (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))
  have p0018 :=
    @g_mp2an (.classMem (syn_cnc (syn_cpw1 (.cv y))) (syn_cncs))
      (.classMem (syn_cnc (.cv z)) (syn_cncs))
      (.classMem (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))) (syn_cncs))
      p0014 p0016 p0017
  have p0019 :=
    @g_ncseqnc (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)))
      (syn_cpw1 (.cv x))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 :=
    @g_n_3bitri
      (.classEq (syn_ctc (syn_cnc (.cv x)))
        (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z))))
      (.classEq (syn_cnc (syn_cpw1 (.cv x)))
        (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))))
      (.classEq (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)))
        (syn_cnc (syn_cpw1 (.cv x))))
      (.classMem (syn_cpw1 (.cv x)) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))))
      p0011 p0012 p0020
  have p0022 :=
    @g_eladdc (syn_cpw1 (.cv x)) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)) a b
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
  have p0023 := @g_vex a
  have p0024 := @g_vex b
  have p0025 :=
    @g_pw1equn c w (.cv a) (.cv b) (.cv x) dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 p0023 p0024
  have p0026 :=
    @g_simp3 (.classEq (.cv x) (syn_cun (.cv c) (.cv w)))
      (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w)))
  have p0027 := @g_elnc (.cv b) (.cv z)
  have p0028 := @g_ensym (.cv b) (.cv z)
  have p0029 := @g_breq2 (.cv b) (syn_cpw1 (.cv w)) (.cv z) (syn_cen)
  have p0030 :=
    @g_biimpcd (.classEq (.cv b) (syn_cpw1 (.cv w))) (syn_wbr (.cv z) (syn_cen) (.cv b))
      (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) p0029
  have p0031 :=
    @g_sylbi (syn_wbr (.cv b) (syn_cen) (.cv z)) (syn_wbr (.cv z) (syn_cen) (.cv b))
      (.imp (.classEq (.cv b) (syn_cpw1 (.cv w)))
        (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))
      p0028 p0030
  have p0032 :=
    @g_sylbi (.classMem (.cv b) (syn_cnc (.cv z))) (syn_wbr (.cv b) (syn_cen) (.cv z))
      (.imp (.classEq (.cv b) (syn_cpw1 (.cv w)))
        (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))
      p0027 p0031
  have p0033 :=
    @g_syl5
      (syn_w3a (.classEq (.cv x) (syn_cun (.cv c) (.cv w)))
        (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w))))
      (.classEq (.cv b) (syn_cpw1 (.cv w))) (.classMem (.cv b) (syn_cnc (.cv z)))
      (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) p0026 p0032
  have p0034 :=
    @g_eximdv (.classMem (.cv b) (syn_cnc (.cv z)))
      (syn_w3a (.classEq (.cv x) (syn_cun (.cv c) (.cv w)))
        (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w))))
      (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) w dv_cache_0026 p0033
  have p0035 :=
    @g_exlimdv (.classMem (.cv b) (syn_cnc (.cv z)))
      (syn_wex w (syn_w3a (.classEq (.cv x) (syn_cun (.cv c) (.cv w)))
          (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w)))))
      (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) c dv_cache_0027
      dv_cache_0028 p0034
  have p0036 :=
    @g_syl5bi (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b)))
      (syn_wex c (syn_wex w (syn_w3a (.classEq (.cv x) (syn_cun (.cv c) (.cv w)))
            (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w))))))
      (.classMem (.cv b) (syn_cnc (.cv z)))
      (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0025 p0035
  have p0037 :=
    @g_adantld (.classMem (.cv b) (syn_cnc (.cv z)))
      (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b)))
      (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0036
  have p0038 :=
    @g_rexlimiv
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b))))
      (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) b (syn_cnc (.cv z))
      dv_cache_0029 p0037
  have p0039 :=
    @g_rexlimivw
      (syn_wrex b (syn_cnc (.cv z)) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b)))))
      (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) a
      (syn_cnc (syn_cpw1 (.cv y))) dv_cache_0030 p0038
  have p0040 :=
    @g_sylbi
      (.classMem (syn_cpw1 (.cv x)) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))))
      (syn_wrex a (syn_cnc (syn_cpw1 (.cv y))) (syn_wrex b (syn_cnc (.cv z))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b))))))
      (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0022 p0039
  have p0041 :=
    @g_sylbi
      (.classEq (syn_ctc (syn_cnc (.cv x)))
        (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z))))
      (.classMem (syn_cpw1 (.cv x)) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))))
      (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0021 p0040
  have p0042 := @g_tceq A (syn_cnc (.cv x))
  have p0043 :=
    @g_n_3ad2ant1 (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
      (.classEq (syn_ctc A) (syn_ctc (syn_cnc (.cv x)))) (.classEq X (syn_cnc (.cv z)))
      p0042
  have p0044 := @g_tceq B (syn_cnc (.cv y))
  have p0045 :=
    @g_adantr (.classEq B (syn_cnc (.cv y)))
      (.classEq (syn_ctc B) (syn_ctc (syn_cnc (.cv y)))) (.classEq X (syn_cnc (.cv z)))
      p0044
  have p0046 := @g_simpr (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z)))
  have p0047 :=
    @g_addceq12d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z))))
      (syn_ctc B) (syn_ctc (syn_cnc (.cv y))) X (syn_cnc (.cv z)) p0045 p0046
  have p0048 :=
    @g_n_3adant1 (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z)))
      (.classEq (syn_cplc (syn_ctc B) X)
        (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z))))
      (.classEq A (syn_cnc (.cv x))) p0047
  have p0049 :=
    @g_eqeq12d
      (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
        (.classEq X (syn_cnc (.cv z))))
      (syn_ctc A) (syn_ctc (syn_cnc (.cv x))) (syn_cplc (syn_ctc B) X)
      (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z))) p0043 p0048
  have p0050 := @g_eqeq1 X (syn_cnc (.cv z)) (syn_cnc (syn_cpw1 (.cv w)))
  have p0051 := @g_eqnc (.cv z) (syn_cpw1 (.cv w)) p0015
  have p0052 :=
    @g_syl6bb (.classEq X (syn_cnc (.cv z))) (.classEq X (syn_cnc (syn_cpw1 (.cv w))))
      (.classEq (syn_cnc (.cv z)) (syn_cnc (syn_cpw1 (.cv w))))
      (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) p0050 p0051
  have p0053 :=
    @g_exbidv (.classEq X (syn_cnc (.cv z))) (.classEq X (syn_cnc (syn_cpw1 (.cv w))))
      (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) w dv_cache_0031 p0052
  have p0054 :=
    @g_n_3ad2ant3 (.classEq X (syn_cnc (.cv z))) (.classEq A (syn_cnc (.cv x)))
      (syn_wb (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w)))))
        (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))))
      (.classEq B (syn_cnc (.cv y))) p0053
  have p0055 :=
    @g_imbi12d
      (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
        (.classEq X (syn_cnc (.cv z))))
      (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
      (.classEq (syn_ctc (syn_cnc (.cv x)))
        (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z))))
      (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w)))))
      (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0049 p0054
  have p0056 :=
    @g_mpbiri
      (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
        (.classEq X (syn_cnc (.cv z))))
      (.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
        (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))
      (.imp (.classEq (syn_ctc (syn_cnc (.cv x)))
          (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z))))
        (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))))
      p0041 p0055
  have p0057 :=
    @g_exlimiv
      (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
        (.classEq X (syn_cnc (.cv z))))
      (.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
        (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))
      z dv_cache_0032 p0056
  have p0058 :=
    @g_exlimivv
      (syn_wex z (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
          (.classEq X (syn_cnc (.cv z)))))
      (.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
        (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))
      x y dv_cache_0033 dv_cache_0034 p0057
  have p0059 :=
    @g_sylbi
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem X (syn_cncs)))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))
              (.classEq X (syn_cnc (.cv z)))))))
      (.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
        (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))
      p0005 p0058
  have p0060 :=
    @g_imp
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem X (syn_cncs)))
      (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))
      (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) p0059
  have p0061 := (Nominal.biimpRefl (syn_wrex c (syn_cncs) (.classEq X (syn_ctc (.cv c)))))
  have p0062 := @g_elncs w (.cv c) dv_cache_0035
  have p0063 :=
    @g_anbi1i (.classMem (.cv c) (syn_cncs))
      (syn_wex w (.classEq (.cv c) (syn_cnc (.cv w)))) (.classEq X (syn_ctc (.cv c)))
      p0062
  have p0064 :=
    @g_n_19_41v (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))) w
      dv_cache_0036
  have p0065 :=
    @g_bitr4i (syn_wa (.classMem (.cv c) (syn_cncs)) (.classEq X (syn_ctc (.cv c))))
      (syn_wa (syn_wex w (.classEq (.cv c) (syn_cnc (.cv w)))) (.classEq X (syn_ctc (.cv c))))
      (syn_wex w (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c)))))
      p0063 p0064
  have p0066 :=
    @g_exbii (syn_wa (.classMem (.cv c) (syn_cncs)) (.classEq X (syn_ctc (.cv c))))
      (syn_wex w (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c)))))
      c p0065
  have p0067 :=
    @g_excom (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))))
      c w
  have p0068 := @g_ncex (.cv w)
  have p0069 := @g_tceq (.cv c) (syn_cnc (.cv w))
  have p0070 := @g_vex w
  have p0071 := @g_tcnc (.cv w) p0070
  have p0072 :=
    @g_syl6eq (.classEq (.cv c) (syn_cnc (.cv w))) (syn_ctc (.cv c))
      (syn_ctc (syn_cnc (.cv w))) (syn_cnc (syn_cpw1 (.cv w))) p0069 p0071
  have p0073 :=
    @g_eqeq2d (.classEq (.cv c) (syn_cnc (.cv w))) (syn_ctc (.cv c))
      (syn_cnc (syn_cpw1 (.cv w))) X p0072
  have p0074 :=
    @g_ceqsexv (.classEq X (syn_ctc (.cv c))) (.classEq X (syn_cnc (syn_cpw1 (.cv w)))) c
      (syn_cnc (.cv w)) dv_cache_0037 dv_cache_0038 p0068 p0073
  have p0075 :=
    @g_exbii
      (syn_wex c (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c)))))
      (.classEq X (syn_cnc (syn_cpw1 (.cv w)))) w p0074
  have p0076 :=
    @g_bitri
      (syn_wex c (syn_wex w
          (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))))))
      (syn_wex w (syn_wex c
          (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))))))
      (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) p0067 p0075
  have p0077 :=
    @g_n_3bitri (syn_wrex c (syn_cncs) (.classEq X (syn_ctc (.cv c))))
      (syn_wex c (syn_wa (.classMem (.cv c) (syn_cncs)) (.classEq X (syn_ctc (.cv c)))))
      (syn_wex c (syn_wex w
          (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))))))
      (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) p0061 p0066 p0076
  have p0078 :=
    @g_sylibr
      (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem X (syn_cncs))) (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)))
      (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w)))))
      (syn_wrex c (syn_cncs) (.classEq X (syn_ctc (.cv c)))) p0060 p0077
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

@[expose]
noncomputable def g_tlecg (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wb (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)))) :=
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
  have dv_cache_0003 : p ∉ ((syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))).fv :=
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
  have dv_cache_0004 : p ∉ ((Wff.classMem M (syn_cncs))).fv :=
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
  have dv_cache_0005 : p ∉ ((syn_ctc M)).fv :=
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
  have dv_cache_0006 : p ∉ ((syn_ctc N)).fv :=
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
  have dv_cache_0008 : q ∉ ((syn_wbr M (syn_clec) N)).fv :=
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
      ((syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
          (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))).fv :=
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
  have dv_cache_0010 : p ∉ ((syn_wbr M (syn_clec) N)).fv :=
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
    p ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv :=
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
  have p0000 := @g_dflec2 M N p dv_cache_0001 dv_cache_0002
  have p0001 := @g_tccl M
  have p0002 := @g_tccl (.cv p)
  have p0003 := @g_addlecncs (syn_ctc M) (syn_ctc (.cv p))
  have p0004 :=
    @g_syl2an (.classMem M (syn_cncs)) (.classMem (syn_ctc M) (syn_cncs))
      (.classMem (syn_ctc (.cv p)) (syn_cncs))
      (syn_wbr (syn_ctc M) (syn_clec) (syn_cplc (syn_ctc M) (syn_ctc (.cv p))))
      (.classMem (.cv p) (syn_cncs)) p0001 p0002 p0003
  have p0005 := @g_tcdi M (.cv p)
  have p0006 :=
    @g_breqtrrd (syn_wa (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs)))
      (syn_ctc M) (syn_cplc (syn_ctc M) (syn_ctc (.cv p))) (syn_ctc (syn_cplc M (.cv p)))
      (syn_clec) p0004 p0005
  have p0007 := @g_tceq N (syn_cplc M (.cv p))
  have p0008 :=
    @g_breq2d (.classEq N (syn_cplc M (.cv p))) (syn_ctc N) (syn_ctc (syn_cplc M (.cv p)))
      (syn_ctc M) (syn_clec) p0007
  have p0009 :=
    @g_syl5ibrcom (syn_wa (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs)))
      (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) (.classEq N (syn_cplc M (.cv p)))
      (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc (syn_cplc M (.cv p)))) p0006 p0008
  have p0010 :=
    @g_rexlimdva (.classMem M (syn_cncs)) (.classEq N (syn_cplc M (.cv p)))
      (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) p (syn_cncs) dv_cache_0003
      dv_cache_0004 p0009
  have p0011 :=
    @g_adantr (.classMem M (syn_cncs))
      (.imp (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))
        (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)))
      (.classMem N (syn_cncs)) p0010
  have p0012 :=
    @g_sylbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr M (syn_clec) N) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))
      (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) p0000 p0011
  have p0013 := @g_tccl N
  have p0014 := @g_dflec2 (syn_ctc M) (syn_ctc N) p dv_cache_0005 dv_cache_0006
  have p0015 :=
    @g_syl2an (.classMem M (syn_cncs)) (.classMem (syn_ctc M) (syn_cncs))
      (.classMem (syn_ctc N) (syn_cncs))
      (syn_wb (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))
        (syn_wrex p (syn_cncs) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))))
      (.classMem N (syn_cncs)) p0001 p0013 p0014
  have p0016 :=
    @g_simplr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wa (.classMem (.cv p) (syn_cncs))
        (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))
  have p0017 :=
    @g_simpll (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wa (.classMem (.cv p) (syn_cncs))
        (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))
  have p0018 :=
    @g_simprl (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
  have p0019 :=
    @g_simprr (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
  have p0020 := @g_taddc N M (.cv p) q dv_cache_0007
  have p0021 :=
    @g_syl31anc
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wa (.classMem (.cv p) (syn_cncs))
          (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))))
      (.classMem N (syn_cncs)) (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs))
      (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
      (syn_wrex q (syn_cncs) (.classEq (.cv p) (syn_ctc (.cv q)))) p0016 p0017 p0018 p0019
      p0020
  have p0022 := @g_addceq2 (.cv p) (syn_ctc (.cv q)) (syn_ctc M)
  have p0023 :=
    @g_eqeq2d (.classEq (.cv p) (syn_ctc (.cv q))) (syn_cplc (syn_ctc M) (.cv p))
      (syn_cplc (syn_ctc M) (syn_ctc (.cv q))) (syn_ctc N) p0022
  have p0024 :=
    @g_biimpac (.classEq (.cv p) (syn_ctc (.cv q)))
      (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
      (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (syn_ctc (.cv q)))) p0023
  have p0025 := @g_tcdi M (.cv q)
  have p0026 :=
    @g_adantlr (.classMem M (syn_cncs)) (.classMem (.cv q) (syn_cncs))
      (.classEq (syn_ctc (syn_cplc M (.cv q))) (syn_cplc (syn_ctc M) (syn_ctc (.cv q))))
      (.classMem N (syn_cncs)) p0025
  have p0027 :=
    @g_eqeq2d
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (syn_ctc (syn_cplc M (.cv q))) (syn_cplc (syn_ctc M) (syn_ctc (.cv q))) (syn_ctc N)
      p0026
  have p0028 :=
    @g_simplr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (.classMem (.cv q) (syn_cncs))
  have p0029 := @g_ncaddccl M (.cv q)
  have p0030 :=
    @g_adantlr (.classMem M (syn_cncs)) (.classMem (.cv q) (syn_cncs))
      (.classMem (syn_cplc M (.cv q)) (syn_cncs)) (.classMem N (syn_cncs)) p0029
  have p0031 := @g_tc11 N (syn_cplc M (.cv q))
  have p0032 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (.classMem N (syn_cncs)) (.classMem (syn_cplc M (.cv q)) (syn_cncs))
      (syn_wb (.classEq (syn_ctc N) (syn_ctc (syn_cplc M (.cv q))))
        (.classEq N (syn_cplc M (.cv q))))
      p0028 p0030 p0031
  have p0033 := @g_addlecncs M (.cv q)
  have p0034 := @g_breq2 N (syn_cplc M (.cv q)) M (syn_clec)
  have p0035 :=
    @g_syl5ibrcom (syn_wa (.classMem M (syn_cncs)) (.classMem (.cv q) (syn_cncs)))
      (syn_wbr M (syn_clec) N) (.classEq N (syn_cplc M (.cv q)))
      (syn_wbr M (syn_clec) (syn_cplc M (.cv q))) p0033 p0034
  have p0036 :=
    @g_adantlr (.classMem M (syn_cncs)) (.classMem (.cv q) (syn_cncs))
      (.imp (.classEq N (syn_cplc M (.cv q))) (syn_wbr M (syn_clec) N))
      (.classMem N (syn_cncs)) p0035
  have p0037 :=
    @g_sylbid
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq (syn_ctc N) (syn_ctc (syn_cplc M (.cv q))))
      (.classEq N (syn_cplc M (.cv q))) (syn_wbr M (syn_clec) N) p0032 p0036
  have p0038 :=
    @g_sylbird
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (syn_ctc (.cv q))))
      (.classEq (syn_ctc N) (syn_ctc (syn_cplc M (.cv q)))) (syn_wbr M (syn_clec) N) p0027
      p0037
  have p0039 :=
    @g_syl5
      (syn_wa (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
        (.classEq (.cv p) (syn_ctc (.cv q))))
      (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (syn_ctc (.cv q))))
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (syn_wbr M (syn_clec) N) p0024 p0038
  have p0040 :=
    @g_expdimp
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
      (.classEq (.cv p) (syn_ctc (.cv q))) (syn_wbr M (syn_clec) N) p0039
  have p0041 :=
    @g_an32s (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classMem (.cv q) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
      (.imp (.classEq (.cv p) (syn_ctc (.cv q))) (syn_wbr M (syn_clec) N)) p0040
  have p0042 :=
    @g_rexlimdva
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))
      (.classEq (.cv p) (syn_ctc (.cv q))) (syn_wbr M (syn_clec) N) q (syn_cncs)
      dv_cache_0008 dv_cache_0009 p0041
  have p0043 :=
    @g_adantrl (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
      (.imp (syn_wrex q (syn_cncs) (.classEq (.cv p) (syn_ctc (.cv q))))
        (syn_wbr M (syn_clec) N))
      (.classMem (.cv p) (syn_cncs)) p0042
  have p0044 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (syn_wa (.classMem (.cv p) (syn_cncs))
          (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))))
      (syn_wrex q (syn_cncs) (.classEq (.cv p) (syn_ctc (.cv q))))
      (syn_wbr M (syn_clec) N) p0021 p0043
  have p0045 :=
    @g_expr (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
      (syn_wbr M (syn_clec) N) p0044
  have p0046 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (syn_wbr M (syn_clec) N) p
      (syn_cncs) dv_cache_0010 dv_cache_0011 p0045
  have p0047 :=
    @g_sylbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))
      (syn_wrex p (syn_cncs) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))
      (syn_wbr M (syn_clec) N) p0015 p0046
  have p0048 :=
    @g_impbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) p0012 p0047
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

@[expose]
noncomputable def g_letc (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
          (syn_wbr M (syn_clec) (syn_ctc N)))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))) :=
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
  have dv_cache_0002 : q ∉ ((syn_ctc N)).fv :=
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
  have dv_cache_0006 : a ∉ ((Wff.classEq (.cv q) (syn_cnc (.cv c)))).fv :=
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
  have dv_cache_0007 : b ∉ ((Wff.classEq (.cv q) (syn_cnc (.cv c)))).fv :=
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
  have dv_cache_0008 : b ∉ ((Wff.classEq M (syn_cnc (.cv a)))).fv :=
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
  have dv_cache_0009 : c ∉ ((Wff.classEq M (syn_cnc (.cv a)))).fv :=
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
  have dv_cache_0010 : a ∉ ((Wff.classEq N (syn_cnc (.cv b)))).fv :=
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
  have dv_cache_0011 : c ∉ ((Wff.classEq N (syn_cnc (.cv b)))).fv :=
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
  have dv_cache_0014 : x ∉ ((syn_cpw1 (.cv b))).fv :=
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
  have dv_cache_0015 : y ∉ ((syn_cpw1 (.cv b))).fv :=
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
  have dv_cache_0016 : x ∉ ((syn_cnc (.cv a))).fv :=
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
  have dv_cache_0017 : y ∉ ((syn_cnc (.cv a))).fv :=
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
  have dv_cache_0018 : x ∉ ((syn_cnc (.cv c))).fv :=
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
  have dv_cache_0019 : y ∉ ((syn_cnc (.cv c))).fv :=
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
  have dv_cache_0028 : p ∉ ((syn_cnc (.cv n))).fv :=
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
  have dv_cache_0029 : p ∉ ((syn_cncs)).fv :=
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
    p ∉ ((Wff.classEq (syn_cnc (.cv a)) (syn_cnc (syn_cpw1 (.cv n))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a)))
              (.classMem (.cv y) (syn_cnc (.cv c))))
            (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))
          (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a)))
              (.classMem (.cv y) (syn_cnc (.cv c))))
            (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))
          (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))))).fv :=
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
    x ∉ ((syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))).fv :=
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
    y ∉ ((syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))).fv :=
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
  have dv_cache_0035 : p ∉ ((Wff.classEq M (syn_cnc (.cv a)))).fv :=
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
      ((Wff.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
          (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))).fv :=
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
      ((Wff.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
          (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))).fv :=
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
      ((Wff.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
          (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))).fv :=
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
  have dv_cache_0039 : q ∉ ((syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))).fv :=
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
    q ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv :=
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
  have p0000 := @g_tccl N
  have p0001 := @g_dflec2 M (syn_ctc N) q dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_sylan2 (.classMem N (syn_cncs)) (.classMem M (syn_cncs))
      (.classMem (syn_ctc N) (syn_cncs))
      (syn_wb (syn_wbr M (syn_clec) (syn_ctc N))
        (syn_wrex q (syn_cncs) (.classEq (syn_ctc N) (syn_cplc M (.cv q)))))
      p0000 p0001
  have p0003 := @g_elncs a M dv_cache_0003
  have p0004 := @g_elncs b N dv_cache_0004
  have p0005 := @g_elncs c (.cv q) dv_cache_0005
  have p0006 :=
    @g_n_3anbi123i (.classMem M (syn_cncs)) (syn_wex a (.classEq M (syn_cnc (.cv a))))
      (.classMem N (syn_cncs)) (syn_wex b (.classEq N (syn_cnc (.cv b))))
      (.classMem (.cv q) (syn_cncs)) (syn_wex c (.classEq (.cv q) (syn_cnc (.cv c))))
      p0003 p0004 p0005
  have p0007 :=
    @g_eeeanv (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
      (.classEq (.cv q) (syn_cnc (.cv c))) a b c dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0008 :=
    @g_bitr4i
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (.classMem (.cv q) (syn_cncs)))
      (syn_w3a (syn_wex a (.classEq M (syn_cnc (.cv a))))
        (syn_wex b (.classEq N (syn_cnc (.cv b))))
        (syn_wex c (.classEq (.cv q) (syn_cnc (.cv c)))))
      (syn_wex a (syn_wex b (syn_wex c
            (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
              (.classEq (.cv q) (syn_cnc (.cv c)))))))
      p0006 p0007
  have p0009 :=
    @g_eqcom (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))
  have p0010 := @g_vex a
  have p0011 := @g_ncelncsi (.cv a) p0010
  have p0012 := @g_vex c
  have p0013 := @g_ncelncsi (.cv c) p0012
  have p0014 := @g_ncaddccl (syn_cnc (.cv a)) (syn_cnc (.cv c))
  have p0015 :=
    @g_mp2an (.classMem (syn_cnc (.cv a)) (syn_cncs))
      (.classMem (syn_cnc (.cv c)) (syn_cncs))
      (.classMem (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))) (syn_cncs)) p0011 p0013
      p0014
  have p0016 :=
    @g_ncseqnc (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))) (syn_cpw1 (.cv b))
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @g_bitri
      (.classEq (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))))
      (.classEq (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))) (syn_cnc (syn_cpw1 (.cv b))))
      (.classMem (syn_cpw1 (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) p0009
      p0017
  have p0019 :=
    @g_eladdc (syn_cpw1 (.cv b)) (syn_cnc (.cv a)) (syn_cnc (.cv c)) x y dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0020 := @g_vex x
  have p0021 := @g_vex y
  have p0022 :=
    @g_pw1equn n m (.cv x) (.cv y) (.cv b) dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 p0020 p0021
  have p0023 := @g_eleq1 (.cv x) (syn_cpw1 (.cv n)) (syn_cnc (.cv a))
  have p0024 := @g_eleq1 (.cv y) (syn_cpw1 (.cv m)) (syn_cnc (.cv c))
  have p0025 :=
    @g_bi2anan9 (.classEq (.cv x) (syn_cpw1 (.cv n)))
      (.classMem (.cv x) (syn_cnc (.cv a)))
      (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a)))
      (.classEq (.cv y) (syn_cpw1 (.cv m))) (.classMem (.cv y) (syn_cnc (.cv c)))
      (.classMem (syn_cpw1 (.cv m)) (syn_cnc (.cv c))) p0023 p0024
  have p0026 := @g_ineq12 (.cv x) (syn_cpw1 (.cv n)) (.cv y) (syn_cpw1 (.cv m))
  have p0027 :=
    @g_eqeq1d
      (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m))))
      (syn_cin (.cv x) (.cv y)) (syn_cin (syn_cpw1 (.cv n)) (syn_cpw1 (.cv m))) (syn_c0)
      p0026
  have p0028 :=
    @g_anbi12d
      (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m))))
      (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c))))
      (syn_wa (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a)))
        (.classMem (syn_cpw1 (.cv m)) (syn_cnc (.cv c))))
      (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
      (.classEq (syn_cin (syn_cpw1 (.cv n)) (syn_cpw1 (.cv m))) (syn_c0)) p0025 p0027
  have p0029 := @g_ncseqnc (syn_cnc (.cv a)) (syn_cpw1 (.cv n))
  have p0030 := Nominal.mp p0011 p0029
  have p0031 := @g_vex n
  have p0032 := @g_ncelncsi (.cv n) p0031
  have p0033 := @g_tceq (.cv p) (syn_cnc (.cv n))
  have p0034 := @g_tcnc (.cv n) p0031
  have p0035 :=
    @g_syl6eq (.classEq (.cv p) (syn_cnc (.cv n))) (syn_ctc (.cv p))
      (syn_ctc (syn_cnc (.cv n))) (syn_cnc (syn_cpw1 (.cv n))) p0033 p0034
  have p0036 :=
    @g_eqeq2d (.classEq (.cv p) (syn_cnc (.cv n))) (syn_ctc (.cv p))
      (syn_cnc (syn_cpw1 (.cv n))) (syn_cnc (.cv a)) p0035
  have p0037 :=
    @g_rspcev (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))
      (.classEq (syn_cnc (.cv a)) (syn_cnc (syn_cpw1 (.cv n)))) p (syn_cnc (.cv n))
      (syn_cncs) dv_cache_0028 dv_cache_0029 dv_cache_0030 p0036
  have p0038 :=
    @g_mpan (.classMem (syn_cnc (.cv n)) (syn_cncs))
      (.classEq (syn_cnc (.cv a)) (syn_cnc (syn_cpw1 (.cv n))))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0032 p0037
  have p0039 :=
    @g_sylbir (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a)))
      (.classEq (syn_cnc (.cv a)) (syn_cnc (syn_cpw1 (.cv n))))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0030 p0038
  have p0040 :=
    @g_ad2antrr (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a)))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))
      (.classMem (syn_cpw1 (.cv m)) (syn_cnc (.cv c)))
      (.classEq (syn_cin (syn_cpw1 (.cv n)) (syn_cpw1 (.cv m))) (syn_c0)) p0039
  have p0041 :=
    @g_syl6bi
      (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a)))
          (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a)))
          (.classMem (syn_cpw1 (.cv m)) (syn_cnc (.cv c))))
        (.classEq (syn_cin (syn_cpw1 (.cv n)) (syn_cpw1 (.cv m))) (syn_c0)))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0028 p0040
  have p0042 :=
    @g_n_3adant1 (.classEq (.cv x) (syn_cpw1 (.cv n)))
      (.classEq (.cv y) (syn_cpw1 (.cv m)))
      (.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a)))
            (.classMem (.cv y) (syn_cnc (.cv c))))
          (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))
        (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))))
      (.classEq (.cv b) (syn_cun (.cv n) (.cv m))) p0041
  have p0043 :=
    @g_exlimivv
      (syn_w3a (.classEq (.cv b) (syn_cun (.cv n) (.cv m)))
        (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m))))
      (.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a)))
            (.classMem (.cv y) (syn_cnc (.cv c))))
          (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))
        (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))))
      n m dv_cache_0031 dv_cache_0032 p0042
  have p0044 :=
    @g_com12
      (syn_wex n (syn_wex m (syn_w3a (.classEq (.cv b) (syn_cun (.cv n) (.cv m)))
            (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m))))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a)))
          (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0043
  have p0045 :=
    @g_syl5bi (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv x) (.cv y)))
      (syn_wex n (syn_wex m (syn_w3a (.classEq (.cv b) (syn_cun (.cv n) (.cv m)))
            (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m))))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a)))
          (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0022 p0044
  have p0046 :=
    @g_expimpd
      (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c))))
      (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
      (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv x) (.cv y)))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0045
  have p0047 :=
    @g_rexlimivv
      (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
        (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv x) (.cv y))))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) x y
      (syn_cnc (.cv a)) (syn_cnc (.cv c)) dv_cache_0017 dv_cache_0033 dv_cache_0034
      dv_cache_0020 p0046
  have p0048 :=
    @g_sylbi (.classMem (syn_cpw1 (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))))
      (syn_wrex x (syn_cnc (.cv a)) (syn_wrex y (syn_cnc (.cv c))
          (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
            (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv x) (.cv y))))))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0019 p0047
  have p0049 :=
    @g_sylbi
      (.classEq (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))))
      (.classMem (syn_cpw1 (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0018 p0048
  have p0050 := @g_tceq N (syn_cnc (.cv b))
  have p0051 := @g_vex b
  have p0052 := @g_tcnc (.cv b) p0051
  have p0053 :=
    @g_syl6eq (.classEq N (syn_cnc (.cv b))) (syn_ctc N) (syn_ctc (syn_cnc (.cv b)))
      (syn_cnc (syn_cpw1 (.cv b))) p0050 p0052
  have p0054 :=
    @g_n_3ad2ant2 (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a)))
      (.classEq (syn_ctc N) (syn_cnc (syn_cpw1 (.cv b))))
      (.classEq (.cv q) (syn_cnc (.cv c))) p0053
  have p0055 := @g_addceq12 M (.cv q) (syn_cnc (.cv a)) (syn_cnc (.cv c))
  have p0056 :=
    @g_n_3adant2 (.classEq M (syn_cnc (.cv a))) (.classEq (.cv q) (syn_cnc (.cv c)))
      (.classEq (syn_cplc M (.cv q)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))))
      (.classEq N (syn_cnc (.cv b))) p0055
  have p0057 :=
    @g_eqeq12d
      (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
        (.classEq (.cv q) (syn_cnc (.cv c))))
      (syn_ctc N) (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc M (.cv q))
      (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))) p0054 p0056
  have p0058 := @g_eqeq1 M (syn_cnc (.cv a)) (syn_ctc (.cv p))
  have p0059 :=
    @g_rexbidv (.classEq M (syn_cnc (.cv a))) (.classEq M (syn_ctc (.cv p)))
      (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))) p (syn_cncs) dv_cache_0035 p0058
  have p0060 :=
    @g_n_3ad2ant1 (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
      (syn_wb (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))
        (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))))
      (.classEq (.cv q) (syn_cnc (.cv c))) p0059
  have p0061 :=
    @g_imbi12d
      (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
        (.classEq (.cv q) (syn_cnc (.cv c))))
      (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
      (.classEq (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))
      (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0057 p0060
  have p0062 :=
    @g_mpbiri
      (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
        (.classEq (.cv q) (syn_cnc (.cv c))))
      (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))
      (.imp (.classEq (syn_cnc (syn_cpw1 (.cv b)))
          (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))))
        (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))))
      p0049 p0061
  have p0063 :=
    @g_exlimiv
      (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
        (.classEq (.cv q) (syn_cnc (.cv c))))
      (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))
      c dv_cache_0036 p0062
  have p0064 :=
    @g_exlimivv
      (syn_wex c (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
          (.classEq (.cv q) (syn_cnc (.cv c)))))
      (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))
      a b dv_cache_0037 dv_cache_0038 p0063
  have p0065 :=
    @g_sylbi
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (.classMem (.cv q) (syn_cncs)))
      (syn_wex a (syn_wex b (syn_wex c
            (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))
              (.classEq (.cv q) (syn_cnc (.cv c)))))))
      (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))
      p0008 p0064
  have p0066 :=
    @g_n_3expa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (.classMem (.cv q) (syn_cncs))
      (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
        (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))
      p0065
  have p0067 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.classEq (syn_ctc N) (syn_cplc M (.cv q)))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))) q (syn_cncs) dv_cache_0039
      dv_cache_0040 p0066
  have p0068 :=
    @g_sylbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (syn_wbr M (syn_clec) (syn_ctc N))
      (syn_wrex q (syn_cncs) (.classEq (syn_ctc N) (syn_cplc M (.cv q))))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))) p0002 p0067
  have p0069 :=
    @g_n_3impia (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (syn_wbr M (syn_clec) (syn_ctc N))
      (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))) p0068
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

@[expose]
noncomputable def g_tlenc1c (M : Class) :
    Nominal.NPrf
      (.imp (.classMem M (syn_cncs)) (syn_wbr (syn_ctc M) (syn_clec) (syn_cnc (syn_c1c)))) :=
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
  have dv_cache_0002 : y ∉ ((syn_cpw1 (.cv x))).fv :=
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
  have dv_cache_0003 : z ∉ ((syn_cpw1 (.cv x))).fv :=
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
  have dv_cache_0004 : z ∉ ((syn_c1c)).fv :=
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
  have dv_cache_0005 : y ∉ ((syn_cnc (syn_cpw1 (.cv x)))).fv :=
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
  have dv_cache_0006 : y ∉ ((syn_cnc (syn_c1c))).fv :=
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
  have dv_cache_0007 : z ∉ ((syn_cnc (syn_c1c))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wss (syn_cpw1 (.cv x)) (.cv z))).fv :=
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
  have dv_cache_0009 : z ∉ ((syn_wss (syn_cpw1 (.cv x)) (syn_c1c))).fv :=
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
  have dv_cache_0011 : x ∉ ((syn_wbr (syn_ctc M) (syn_clec) (syn_cnc (syn_c1c)))).fv :=
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
  have p0000 := @g_elncs x M dv_cache_0001
  have p0001 := @g_tceq M (syn_cnc (.cv x))
  have p0002 := @g_vex x
  have p0003 := @g_tcnc (.cv x) p0002
  have p0004 :=
    @g_syl6eq (.classEq M (syn_cnc (.cv x))) (syn_ctc M) (syn_ctc (syn_cnc (.cv x)))
      (syn_cnc (syn_cpw1 (.cv x))) p0001 p0003
  have p0005 := @g_pw1ex (.cv x) p0002
  have p0006 := @g_ncid (syn_cpw1 (.cv x)) p0005
  have p0007 := @g_n_1cex
  have p0008 := @g_ncid (syn_c1c) p0007
  have p0009 := @g_pw1ss1c (.cv x)
  have p0010 := @g_sseq1 (.cv y) (syn_cpw1 (.cv x)) (.cv z)
  have p0011 := @g_sseq2 (.cv z) (syn_c1c) (syn_cpw1 (.cv x))
  have p0012 :=
    @g_rspc2ev (syn_wss (.cv y) (.cv z)) (syn_wss (syn_cpw1 (.cv x)) (syn_c1c))
      (syn_wss (syn_cpw1 (.cv x)) (.cv z)) y z (syn_cpw1 (.cv x)) (syn_c1c)
      (syn_cnc (syn_cpw1 (.cv x))) (syn_cnc (syn_c1c)) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0010 p0011
  have p0013 :=
    @g_mp3an (.classMem (syn_cpw1 (.cv x)) (syn_cnc (syn_cpw1 (.cv x))))
      (.classMem (syn_c1c) (syn_cnc (syn_c1c))) (syn_wss (syn_cpw1 (.cv x)) (syn_c1c))
      (syn_wrex y (syn_cnc (syn_cpw1 (.cv x)))
        (syn_wrex z (syn_cnc (syn_c1c)) (syn_wss (.cv y) (.cv z))))
      p0006 p0008 p0009 p0012
  have p0014 := @g_ncex (syn_cpw1 (.cv x))
  have p0015 := @g_ncex (syn_c1c)
  have p0016 :=
    @g_brlec y z (syn_cnc (syn_cpw1 (.cv x))) (syn_cnc (syn_c1c)) dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0010 p0014 p0015
  have p0017 :=
    @g_mpbir (syn_wbr (syn_cnc (syn_cpw1 (.cv x))) (syn_clec) (syn_cnc (syn_c1c)))
      (syn_wrex y (syn_cnc (syn_cpw1 (.cv x)))
        (syn_wrex z (syn_cnc (syn_c1c)) (syn_wss (.cv y) (.cv z))))
      p0013 p0016
  have p0018 :=
    @g_syl6eqbr (.classEq M (syn_cnc (.cv x))) (syn_ctc M) (syn_cnc (syn_cpw1 (.cv x)))
      (syn_cnc (syn_c1c)) (syn_clec) p0004 p0017
  have p0019 :=
    @g_exlimiv (.classEq M (syn_cnc (.cv x)))
      (syn_wbr (syn_ctc M) (syn_clec) (syn_cnc (syn_c1c))) x dv_cache_0011 p0018
  have p0020 :=
    @g_sylbi (.classMem M (syn_cncs)) (syn_wex x (.classEq M (syn_cnc (.cv x))))
      (syn_wbr (syn_ctc M) (syn_clec) (syn_cnc (syn_c1c))) p0000 p0019
  exact p0020

@[expose]
noncomputable def g_n_1ne0c : Nominal.NPrf (syn_wne (syn_c1c) (syn_c0c)) :=
  by
  have p0000 := @g_addcid2 (syn_c1c)
  have p0001 := @g_n_0cnsuc (syn_c0c)
  have p0002 := @g_eqnetrri (syn_cplc (syn_c0c) (syn_c1c)) (syn_c1c) (syn_c0c) p0000 p0001
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

@[expose]
noncomputable def g_tcfnex : Nominal.NPrf (.classMem (syn_ctcfn) (syn_cvv)) :=
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
  have dv_cache_0001 : p ∉ ((syn_cop (.cv z) (.cv x))).fv := by
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
      ((syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                  (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))).fv :=
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
  have dv_cache_0003 : q ∉ ((Wff.classMem (.cv p) (syn_cncs))).fv :=
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
  have dv_cache_0004 : t ∉ ((syn_csn (.cv q))).fv :=
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
  have dv_cache_0006 : t ∉ ((syn_cpw1fn)).fv :=
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
  have dv_cache_0007 : t ∉ ((syn_wbr (.cv u) (syn_csset) (.cv p))).fv :=
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
  have dv_cache_0008 : u ∉ ((syn_csn (.cv t))).fv :=
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
      ((syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))
          (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)))).fv :=
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
  have dv_cache_0010 : u ∉ ((syn_csn (syn_csn (.cv q)))).fv :=
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
  have dv_cache_0012 : u ∉ ((syn_csset)).fv :=
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
  have dv_cache_0013 : u ∉ ((syn_csi (syn_cpw1fn))).fv :=
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
  have dv_cache_0014 : t ∉ ((syn_cpw1 (.cv q))).fv :=
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
  have dv_cache_0016 : t ∉ ((syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))).fv :=
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
  have dv_cache_0017 : t ∉ ((syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))).fv :=
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
  have dv_cache_0020 : q ∉ ((syn_cop (.cv p) (.cv x))).fv :=
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
      ((syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))).fv :=
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
  have dv_cache_0022 : z ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv :=
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
      ((syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                  (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                          (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))).fv :=
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
  have dv_cache_0024 : p ∉ ((syn_cuni (.cv x))).fv :=
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
  have dv_cache_0025 : q ∉ ((syn_cuni (.cv x))).fv :=
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
      ((syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
            (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))).fv :=
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
  have dv_cache_0030 : x ∉ ((syn_c1c)).fv :=
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
      ((syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                    (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima
                            (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                        (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))).fv :=
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
      ((syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                    (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima
                            (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                        (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))).fv :=
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
  have dv_cache_0033 : y ∉ ((syn_ctc (syn_cuni (.cv x)))).fv :=
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
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tcfn x
  have p0001 :=
    @g_oteltxp (.cv z) (syn_csn (.cv y)) (.cv x) (syn_ccnv (syn_csset))
      (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv))
                (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                    (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                      (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))
  have p0002 :=
    (Nominal.biimpRefl (syn_wbr (.cv z) (syn_ccnv (syn_csset)) (syn_csn (.cv y))))
  have p0003 := @g_brcnv (.cv z) (syn_csn (.cv y)) (syn_csset)
  have p0004 := @g_vex y
  have p0005 := @g_vex z
  have p0006 := @g_brssetsn (.cv y) (.cv z) p0004 p0005
  have p0007_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv z)) (.objMem y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_bitri (syn_wbr (.cv z) (syn_ccnv (syn_csset)) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv z)) (.objMem y z) p0003
      p0007_e01_recanon
  have p0008 :=
    @g_bitr3i (.classMem (syn_cop (.cv z) (syn_csn (.cv y))) (syn_ccnv (syn_csset)))
      (syn_wbr (.cv z) (syn_ccnv (syn_csset)) (syn_csn (.cv y))) (.objMem y z) p0002 p0007
  have p0009 := @g_vex x
  have p0010 := @g_opex (.cv z) (.cv x) p0005 p0009
  have p0011 :=
    @g_elcompl (syn_cop (.cv z) (.cv x))
      (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                  (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))
      p0010
  have p0012 :=
    @g_elrn2 p (syn_cop (.cv z) (.cv x))
      (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
              (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
              (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))
      dv_cache_0001 dv_cache_0002
  have p0013 :=
    @g_elsymdif (syn_cop (.cv p) (syn_cop (.cv z) (.cv x)))
      (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
            (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
              (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
            (syn_cpw1 (syn_c1c)))))
      (syn_cins3 (syn_cid))
  have p0014 :=
    @g_otelins2 (.cv p) (.cv z) (.cv x)
      (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
          (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c))))
      p0005
  have p0015 :=
    @g_elin (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv))
      (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
        (syn_cpw1 (syn_c1c)))
  have p0016 := @g_opelxp (.cv p) (.cv x) (syn_cncs) (syn_cvv)
  have p0017 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv)))
      (.classMem (.cv p) (syn_cncs)) (.classMem (.cv x) (syn_cvv)) p0009 p0016
  have p0018 :=
    @g_anbi1i (.classMem (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv)))
      (.classMem (.cv p) (syn_cncs))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima
          (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c))))
      p0017
  have p0019 := @g_ncseqnc (.cv p) (syn_cpw1 (.cv q))
  have p0020 :=
    @g_rexbidv (.classMem (.cv p) (syn_cncs))
      (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))
      (.classMem (syn_cpw1 (.cv q)) (.cv p)) q (syn_cuni (.cv x)) dv_cache_0003 p0019
  have p0021 :=
    @g_oteltxp (syn_csn (syn_csn (.cv q))) (.cv p) (.cv x)
      (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))
  have p0022 := @g_snex (.cv q)
  have p0023 :=
    @g_brsnsi1 t (syn_csn (.cv q)) (.cv u) (syn_cpw1fn) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0022
  have p0024 :=
    @g_anbi1i (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u))
      (syn_wex t (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
          (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))))
      (syn_wbr (.cv u) (syn_csset) (.cv p)) p0023
  have p0025 :=
    @g_n_19_41v
      (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
        (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
      (syn_wbr (.cv u) (syn_csset) (.cv p)) t dv_cache_0007
  have p0026 :=
    @g_bitr4i
      (syn_wa (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u))
        (syn_wbr (.cv u) (syn_csset) (.cv p)))
      (syn_wa (syn_wex t (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
            (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))))
        (syn_wbr (.cv u) (syn_csset) (.cv p)))
      (syn_wex t (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
            (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
          (syn_wbr (.cv u) (syn_csset) (.cv p))))
      p0024 p0025
  have p0027 :=
    @g_exbii
      (syn_wa (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u))
        (syn_wbr (.cv u) (syn_csset) (.cv p)))
      (syn_wex t (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
            (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
          (syn_wbr (.cv u) (syn_csset) (.cv p))))
      u p0026
  have p0028 :=
    @g_excom
      (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
          (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
        (syn_wbr (.cv u) (syn_csset) (.cv p)))
      u t
  have p0029 :=
    @g_anass (.classEq (.cv u) (syn_csn (.cv t)))
      (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))
      (syn_wbr (.cv u) (syn_csset) (.cv p))
  have p0030 :=
    @g_exbii
      (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
          (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
        (syn_wbr (.cv u) (syn_csset) (.cv p)))
      (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
        (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))
          (syn_wbr (.cv u) (syn_csset) (.cv p))))
      u p0029
  have p0031 := @g_snex (.cv t)
  have p0032 := @g_breq1 (.cv u) (syn_csn (.cv t)) (.cv p) (syn_csset)
  have p0033 :=
    @g_anbi2d (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p))
      (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p))
      (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) p0032
  have p0034 :=
    @g_ceqsexv
      (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))
        (syn_wbr (.cv u) (syn_csset) (.cv p)))
      (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))
        (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)))
      u (syn_csn (.cv t)) dv_cache_0008 dv_cache_0009 p0031 p0033
  have p0035 := @g_vex q
  have p0036 := @g_brpw1fn (.cv q) (.cv t) p0035
  have p0037 := @g_vex t
  have p0038 := @g_vex p
  have p0039 := @g_brssetsn (.cv t) (.cv p) p0037 p0038
  have p0040_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)) (.objMem t p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_anbi12i (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))
      (.classEq (.cv t) (syn_cpw1 (.cv q)))
      (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)) (.objMem t p) p0036
      p0040_e01_recanon
  have p0041 :=
    @g_n_3bitri
      (syn_wex u (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
            (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
          (syn_wbr (.cv u) (syn_csset) (.cv p))))
      (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
          (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))
            (syn_wbr (.cv u) (syn_csset) (.cv p)))))
      (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))
        (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)))
      (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p)) p0030 p0034 p0040
  have p0042 :=
    @g_exbii
      (syn_wex u (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
            (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
          (syn_wbr (.cv u) (syn_csset) (.cv p))))
      (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p)) t p0041
  have p0043 :=
    @g_n_3bitri
      (syn_wex u (syn_wa (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u))
          (syn_wbr (.cv u) (syn_csset) (.cv p))))
      (syn_wex u (syn_wex t (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
              (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
            (syn_wbr (.cv u) (syn_csset) (.cv p)))))
      (syn_wex t (syn_wex u (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t)))
              (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))
            (syn_wbr (.cv u) (syn_csset) (.cv p)))))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p))) p0027 p0028
      p0042
  have p0044 :=
    @g_opelco u (syn_csn (syn_csn (.cv q))) (.cv p) (syn_csset) (syn_csi (syn_cpw1fn))
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0045 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t
      (syn_cpw1 (.cv q)) (.cv p) dv_cache_0014 dv_cache_0015)
  have p0046_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cpw1 (.cv q)) (.cv p))
        (syn_wex t (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss
          syn_c1c syn_wex syn_csn
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
    @g_n_3bitr4i
      (syn_wex u (syn_wa (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u))
          (syn_wbr (.cv u) (syn_csset) (.cv p))))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv p))
        (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))))
      (.classMem (syn_cpw1 (.cv q)) (.cv p)) p0043 p0044 p0046_e02_recanon
  have p0047 :=
    @g_oteltxp (syn_csn (.cv t)) (syn_csn (syn_csn (.cv q))) (.cv x)
      (syn_csi (syn_ccnv (syn_csset))) (syn_csset)
  have p0048 :=
    (Nominal.biimpRefl (syn_wbr (syn_csn (.cv t)) (syn_csi (syn_ccnv (syn_csset)))
        (syn_csn (syn_csn (.cv q)))))
  have p0049 := @g_brsnsi (.cv t) (syn_csn (.cv q)) (syn_ccnv (syn_csset)) p0037 p0022
  have p0050 := @g_brcnv (.cv t) (syn_csn (.cv q)) (syn_csset)
  have p0051 := @g_brssetsn (.cv q) (.cv t) p0035 p0037
  have p0052_e02_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv q)) (syn_csset) (.cv t)) (.objMem q t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_n_3bitri
      (syn_wbr (syn_csn (.cv t)) (syn_csi (syn_ccnv (syn_csset))) (syn_csn (syn_csn (.cv q))))
      (syn_wbr (.cv t) (syn_ccnv (syn_csset)) (syn_csn (.cv q)))
      (syn_wbr (syn_csn (.cv q)) (syn_csset) (.cv t)) (.objMem q t) p0049 p0050
      p0052_e02_recanon
  have p0053 :=
    @g_bitr3i
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (syn_csn (.cv q))))
        (syn_csi (syn_ccnv (syn_csset))))
      (syn_wbr (syn_csn (.cv t)) (syn_csi (syn_ccnv (syn_csset))) (syn_csn (syn_csn (.cv q))))
      (.objMem q t) p0048 p0052
  have p0054 := @g_opelssetsn (.cv t) (.cv x) p0037 p0009
  have p0055_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv t)) (.cv x)) (syn_csset)) (.objMem t x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (syn_csn (.cv q))))
        (syn_csi (syn_ccnv (syn_csset))))
      (.objMem q t) (.classMem (syn_cop (syn_csn (.cv t)) (.cv x)) (syn_csset))
      (.objMem t x) p0053 p0055_e01_recanon
  have p0056 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x)))
        (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (syn_csn (.cv q))))
          (syn_csi (syn_ccnv (syn_csset))))
        (.classMem (syn_cop (syn_csn (.cv t)) (.cv x)) (syn_csset)))
      (syn_wa (.objMem q t) (.objMem t x)) p0047 p0055
  have p0057 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x)))
        (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)))
      (syn_wa (.objMem q t) (.objMem t x)) t p0056
  have p0058 :=
    @g_elima1c t (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))
      (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) dv_cache_0016 dv_cache_0017
  have p0059 := @g_eluni t (.cv q) (.cv x) dv_cache_0018 dv_cache_0019
  have p0060_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv q) (syn_cuni (.cv x)))
        (syn_wex t (syn_wa (.objMem q t) (.objMem t x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
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
    @g_n_3bitr4i
      (syn_wex t (.classMem
          (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x)))
          (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))))
      (syn_wex t (syn_wa (.objMem q t) (.objMem t x)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))
        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
      (.classMem (.cv q) (syn_cuni (.cv x))) p0057 p0058 p0060_e02_recanon
  have p0061 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv p))
        (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))))
      (.classMem (syn_cpw1 (.cv q)) (.cv p))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))
        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
      (.classMem (.cv q) (syn_cuni (.cv x))) p0046 p0060
  have p0062 :=
    @g_ancom (.classMem (syn_cpw1 (.cv q)) (.cv p)) (.classMem (.cv q) (syn_cuni (.cv x)))
  have p0063 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (syn_cop (.cv p) (.cv x)))
        (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv p))
          (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))))
        (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))
      (syn_wa (.classMem (syn_cpw1 (.cv q)) (.cv p)) (.classMem (.cv q) (syn_cuni (.cv x))))
      (syn_wa (.classMem (.cv q) (syn_cuni (.cv x))) (.classMem (syn_cpw1 (.cv q)) (.cv p)))
      p0021 p0061 p0062
  have p0064 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (syn_cop (.cv p) (.cv x)))
        (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))
      (syn_wa (.classMem (.cv q) (syn_cuni (.cv x))) (.classMem (syn_cpw1 (.cv q)) (.cv p)))
      q p0063
  have p0065 :=
    @g_elimapw11c q (syn_cop (.cv p) (.cv x))
      (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
      dv_cache_0020 dv_cache_0021
  have p0066 :=
    (Nominal.biimpRefl (syn_wrex q (syn_cuni (.cv x)) (.classMem (syn_cpw1 (.cv q)) (.cv p))))
  have p0067 :=
    @g_n_3bitr4i
      (syn_wex q (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (syn_cop (.cv p) (.cv x)))
          (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))))
      (syn_wex q (syn_wa (.classMem (.cv q) (syn_cuni (.cv x)))
          (.classMem (syn_cpw1 (.cv q)) (.cv p))))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima
          (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c))))
      (syn_wrex q (syn_cuni (.cv x)) (.classMem (syn_cpw1 (.cv q)) (.cv p))) p0064 p0065
      p0066
  have p0068 :=
    @g_syl6rbbr (.classMem (.cv p) (syn_cncs))
      (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))
      (syn_wrex q (syn_cuni (.cv x)) (.classMem (syn_cpw1 (.cv q)) (.cv p)))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima
          (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c))))
      p0020 p0067
  have p0069 :=
    @g_pm5_32i (.classMem (.cv p) (syn_cncs))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima
          (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c))))
      (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))
      p0068
  have p0070 :=
    @g_bitri
      (syn_wa (.classMem (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv)))
        (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima
            (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
              (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
            (syn_cpw1 (syn_c1c)))))
      (syn_wa (.classMem (.cv p) (syn_cncs)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima
            (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
              (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
            (syn_cpw1 (syn_c1c)))))
      (syn_wa (.classMem (.cv p) (syn_cncs))
        (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
      p0018 p0069
  have p0071 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins2
          (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
              (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
              (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
            (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
              (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
            (syn_cpw1 (syn_c1c)))))
      (syn_wa (.classMem (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv)))
        (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima
            (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
              (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
            (syn_cpw1 (syn_c1c)))))
      (syn_wa (.classMem (.cv p) (syn_cncs))
        (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
      p0014 p0015 p0070
  have p0072 := @g_otelins3 (.cv p) (.cv z) (.cv x) (syn_cid) p0009
  have p0073 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cid) (.cv z)))
  have p0074 := @g_ideq (.cv p) (.cv z) p0005
  have p0075_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv p) (syn_cid) (.cv z)) (.objEq p z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
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
    @g_bitr3i (.classMem (syn_cop (.cv p) (.cv z)) (syn_cid))
      (syn_wbr (.cv p) (syn_cid) (.cv z)) (.objEq p z) p0073 p0075_e01_recanon
  have p0076 :=
    @g_bitri (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins3 (syn_cid)))
      (.classMem (syn_cop (.cv p) (.cv z)) (syn_cid)) (.objEq p z) p0072 p0075
  have p0077 :=
    @g_bibi12i
      (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins2
          (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
              (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
              (syn_cpw1 (syn_c1c))))))
      (syn_wa (.classMem (.cv p) (syn_cncs))
        (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
      (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins3 (syn_cid)))
      (.objEq p z) p0071 p0076
  have p0078 :=
    @g_xchbinx
      (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_csymdif (syn_cins2
            (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                  (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))
      (syn_wb (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins2
            (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                  (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins3 (syn_cid))))
      (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
          (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
        (.objEq p z))
      p0013 p0077
  have p0079 :=
    @g_exbii
      (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_csymdif (syn_cins2
            (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                  (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))
      (.neg (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
              (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))
      p p0078
  have p0080 :=
    @g_exnal
      (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
          (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
        (.objEq p z))
      p
  have p0081 :=
    @g_n_3bitrri
      (.classMem (syn_cop (.cv z) (.cv x)) (syn_crn (syn_csymdif (syn_cins2
              (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                    (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                      (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))
      (syn_wex p (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_csymdif (syn_cins2
              (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                    (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                      (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))
      (syn_wex p (.neg (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
              (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
            (.objEq p z))))
      (.neg (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
              (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
            (.objEq p z))))
      p0012 p0079 p0080
  have p0082 :=
    @g_con1bii
      (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
              (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))
      (.classMem (syn_cop (.cv z) (.cv x)) (syn_crn (syn_csymdif (syn_cins2
              (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                    (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                      (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))
      p0081
  have p0083 :=
    @g_bitri
      (.classMem (syn_cop (.cv z) (.cv x)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                        (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))
      (.neg (.classMem (syn_cop (.cv z) (.cv x)) (syn_crn (syn_csymdif (syn_cins2
                (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                        (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))
      (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
              (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))
      p0011 p0082
  have p0084 :=
    @g_anbi12i (.classMem (syn_cop (.cv z) (syn_csn (.cv y))) (syn_ccnv (syn_csset)))
      (.objMem y z)
      (.classMem (syn_cop (.cv z) (.cv x)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                        (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))
      (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
              (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))
      p0008 p0083
  have p0085 :=
    @g_bitri
      (.classMem (syn_cop (.cv z) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                  (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                          (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))
      (syn_wa (.classMem (syn_cop (.cv z) (syn_csn (.cv y))) (syn_ccnv (syn_csset)))
        (.classMem (syn_cop (.cv z) (.cv x)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                  (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                          (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))
      (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
              (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
            (.objEq p z))))
      p0001 p0084
  have p0086 :=
    @g_exbii
      (.classMem (syn_cop (.cv z) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                  (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                          (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))
      (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
              (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
            (.objEq p z))))
      z p0085
  have p0087 :=
    @g_elrn2 z (syn_cop (syn_csn (.cv y)) (.cv x))
      (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                        (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))
      dv_cache_0022 dv_cache_0023
  have p0088 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc q
      (syn_cuni (.cv x)) p dv_cache_0024 dv_cache_0025 dv_cache_0026
  have p0089 :=
    @g_dfiota2
      (syn_wa (.classMem (.cv p) (syn_cncs))
        (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
      p z dv_cache_0027 dv_cache_0028
  have p0090 :=
    @g_eqtri (syn_ctc (syn_cuni (.cv x)))
      (syn_cio p (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
            (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))))
      (syn_cuni (.cab z (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
                (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
              (.objEq p z)))))
      p0088 p0089
  have p0091 :=
    @g_eleq2i (syn_ctc (syn_cuni (.cv x)))
      (syn_cuni (.cab z (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
                (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
              (.objEq p z)))))
      (.cv y) p0090
  have p0092 :=
    @g_eluniab
      (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
              (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))
      z (.cv y) dv_cache_0029
  have p0093_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv y) (syn_cuni (.cab z (.all p (syn_wb
                  (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
                      (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))))))
        (syn_wex z (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
                  (syn_wrex q (syn_cuni (.cv x))
                    (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
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
    @g_bitri (.classMem (.cv y) (syn_ctc (syn_cuni (.cv x))))
      (.classMem (.cv y) (syn_cuni (.cab z (.all p (syn_wb
                (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x))
                    (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))))))
      (syn_wex z (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
                (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
              (.objEq p z)))))
      p0091 p0093_e01_recanon
  have p0094 :=
    @g_n_3bitr4i
      (syn_wex z (.classMem (syn_cop (.cv z) (syn_cop (syn_csn (.cv y)) (.cv x)))
          (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                    (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima
                            (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                        (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))))
      (syn_wex z (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs))
                (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))
              (.objEq p z)))))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_crn (syn_ctxp (syn_ccnv (syn_csset))
            (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv))
                      (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                            (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))))
      (.classMem (.cv y) (syn_ctc (syn_cuni (.cv x)))) p0086 p0087 p0093
  have p0095 :=
    @g_releqmpt x y (syn_c1c)
      (syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                  (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                          (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))
      (syn_ctc (syn_cuni (.cv x))) dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 p0094
  have p0096 :=
    @g_eqtr4i (syn_ctcfn) (syn_cmpt x (syn_c1c) (syn_ctc (syn_cuni (.cv x))))
      (syn_cin (syn_cxp (syn_c1c) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_crn
                    (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif
                            (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                                  (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                                    (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset)))
                                        (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))))
                            (syn_cins3 (syn_cid))))))))) (syn_c1c)))))
      p0000 p0095
  have p0097 := @g_n_1cex
  have p0098 := @g_ssetex
  have p0099 := @g_cnvex (syn_csset) p0098
  have p0100 := @g_ncsex
  have p0101 := @g_vvex
  have p0102 := @g_xpex (syn_cncs) (syn_cvv) p0100 p0101
  have p0104 := @g_pw1fnex
  have p0105 := @g_siex (syn_cpw1fn) p0104
  have p0106 := @g_coex (syn_csset) (syn_csi (syn_cpw1fn)) p0098 p0105
  have p0107 := @g_siex (syn_ccnv (syn_csset)) p0099
  have p0109 := @g_txpex (syn_csi (syn_ccnv (syn_csset))) (syn_csset) p0107 p0098
  have p0111 :=
    @g_imaex (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c) p0109 p0097
  have p0112 :=
    @g_txpex (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)) p0106
      p0111
  have p0114 := @g_pw1ex (syn_c1c) p0097
  have p0115 :=
    @g_imaex
      (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
      (syn_cpw1 (syn_c1c)) p0112 p0114
  have p0116 :=
    @g_inex (syn_cxp (syn_cncs) (syn_cvv))
      (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
        (syn_cpw1 (syn_c1c)))
      p0102 p0115
  have p0117 :=
    @g_ins2ex
      (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
          (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c))))
      p0116
  have p0118 := @g_idex
  have p0119 := @g_ins3ex (syn_cid) p0118
  have p0120 :=
    @g_symdifex
      (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
            (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
              (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
            (syn_cpw1 (syn_c1c)))))
      (syn_cins3 (syn_cid)) p0117 p0119
  have p0121 :=
    @g_rnex
      (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
              (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
              (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))
      p0120
  have p0122 :=
    @g_complex
      (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                  (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
                (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))
      p0121
  have p0123 :=
    @g_txpex (syn_ccnv (syn_csset))
      (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv))
                (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                    (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                      (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))
      p0099 p0122
  have p0124 :=
    @g_rnex
      (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                        (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))
      p0123
  have p0125 :=
    @g_mptexlem (syn_c1c)
      (syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2
                  (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                          (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))
      p0097 p0124
  have p0126 :=
    @g_eqeltri (syn_ctcfn)
      (syn_cin (syn_cxp (syn_c1c) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_crn
                    (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif
                            (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima
                                  (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))
                                    (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset)))
                                        (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))))
                            (syn_cins3 (syn_cid))))))))) (syn_c1c)))))
      (syn_cvv) p0096 p0125
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

@[expose]
noncomputable def g_fntcfn : Nominal.NPrf (syn_wfn (syn_ctcfn) (syn_c1c)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_c1c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tcfn x
  have p0001 :=
    @g_fnmpt x (syn_c1c) (syn_ctc (syn_cuni (.cv x))) (syn_ctcfn) (syn_cvv) dv_cache_0001
      p0000
  have p0002 := @g_tcex (syn_cuni (.cv x))
  have p0003 :=
    @g_a1i (.classMem (syn_ctc (syn_cuni (.cv x))) (syn_cvv))
      (.classMem (.cv x) (syn_c1c)) p0002
  have p0004 :=
    @g_mprg (.classMem (syn_ctc (syn_cuni (.cv x))) (syn_cvv))
      (syn_wfn (syn_ctcfn) (syn_c1c)) x (syn_c1c) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_brtcfn (A : Class) (B : Class)
    (hyp_brtcfn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn A) (syn_ctcfn) B) (.classEq B (syn_ctc A))) :=
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
  have dv_cache_0001 : x ∉ ((syn_csn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ctc A)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_c1c)).fv :=
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
  have p0000 := @g_snel1c A hyp_brtcfn_1
  have p0001 := @g_unieq (.cv x) (syn_csn A)
  have p0002 := @g_unisn A hyp_brtcfn_1
  have p0003 :=
    @g_syl6eq (.classEq (.cv x) (syn_csn A)) (syn_cuni (.cv x)) (syn_cuni (syn_csn A)) A
      p0001 p0002
  have p0004 := @g_tceq (syn_cuni (.cv x)) A
  have p0005 :=
    @g_syl (.classEq (.cv x) (syn_csn A)) (.classEq (syn_cuni (.cv x)) A)
      (.classEq (syn_ctc (syn_cuni (.cv x))) (syn_ctc A)) p0003 p0004
  have p0006 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tcfn x
  have p0007 := @g_tcex A
  have p0008 :=
    @g_fvmpt x (syn_csn A) (syn_ctc (syn_cuni (.cv x))) (syn_ctc A) (syn_c1c) (syn_ctcfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0005 p0006 p0007
  have p0009 := Nominal.mp p0000 p0008
  have p0010 := @g_eqeq1i (syn_cfv (syn_ctcfn) (syn_csn A)) (syn_ctc A) B p0009
  have p0011 := @g_fntcfn
  have p0012 := @g_fnbrfvb (syn_c1c) (syn_csn A) B (syn_ctcfn)
  have p0013 :=
    @g_mp2an (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn A) (syn_c1c))
      (syn_wb (.classEq (syn_cfv (syn_ctcfn) (syn_csn A)) B)
        (syn_wbr (syn_csn A) (syn_ctcfn) B))
      p0011 p0000 p0012
  have p0014 := @g_eqcom (syn_ctc A) B
  have p0015 :=
    @g_n_3bitr3i (.classEq (syn_cfv (syn_ctcfn) (syn_csn A)) B) (.classEq (syn_ctc A) B)
      (syn_wbr (syn_csn A) (syn_ctcfn) B) (.classEq B (syn_ctc A)) p0010 p0013 p0014
  exact p0015

@[expose]
noncomputable def g_addcdi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
        (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
          (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cplc B C)).fv := by
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
      ((Wff.imp (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
            (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
              (syn_co A (syn_cmuc) (syn_cnc (.cv z))))))).fv :=
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
      ((Wff.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
          (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))).fv :=
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
      ((Wff.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
          (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))).fv :=
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
      ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs)))).fv :=
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
      ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs)))).fv :=
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
      ((Wff.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
          (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))).fv :=
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
      ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs)))).fv :=
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
  have p0000 := @g_ncaddccl B C
  have p0001 :=
    @g_n_3adant1 (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
      (.classMem (syn_cplc B C) (syn_cncs)) (.classMem A (syn_cncs)) p0000
  have p0002 := @g_elncs x (syn_cplc B C) dv_cache_0001
  have p0003 := @g_vex x
  have p0004 := @g_ncid (.cv x) p0003
  have p0005 := @g_eleq2 (syn_cplc B C) (syn_cnc (.cv x)) (.cv x)
  have p0006 :=
    @g_mpbiri (.classEq (syn_cplc B C) (syn_cnc (.cv x)))
      (.classMem (.cv x) (syn_cplc B C)) (.classMem (.cv x) (syn_cnc (.cv x))) p0004 p0005
  have p0007 :=
    @g_eladdc (.cv x) B C y z dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0008 := @g_ncseqnc B (.cv y)
  have p0009 := @g_ncseqnc C (.cv z)
  have p0010 :=
    @g_bi2anan9 (.classMem B (syn_cncs)) (.classEq B (syn_cnc (.cv y)))
      (.classMem (.cv y) B) (.classMem C (syn_cncs)) (.classEq C (syn_cnc (.cv z)))
      (.classMem (.cv z) C) p0008 p0009
  have p0011 :=
    @g_n_3adant1 (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
      (syn_wb (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z))))
        (syn_wa (.classMem (.cv y) B) (.classMem (.cv z) C)))
      (.classMem A (syn_cncs)) p0010
  have p0012 := @g_elncs x A dv_cache_0009
  have p0013 := @g_vex y
  have p0014 := @g_vex z
  have p0015 := @g_ncdisjun (.cv y) (.cv z) p0013 p0014
  have p0016 :=
    @g_oveq2d (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (syn_cnc (syn_cun (.cv y) (.cv z))) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))
      (syn_cnc (.cv x)) (syn_cmuc) p0015
  have p0017 := @g_xpdisj2 (.cv y) (.cv z) (.cv x) (.cv x)
  have p0018 := @g_xpex (.cv x) (.cv y) p0003 p0013
  have p0019 := @g_xpex (.cv x) (.cv z) p0003 p0014
  have p0020 :=
    @g_ncdisjun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z)) p0018 p0019
  have p0021 :=
    @g_syl (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (.classEq (syn_cin (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z))) (syn_c0))
      (.classEq (syn_cnc (syn_cun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z))))
        (syn_cplc (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cnc (syn_cxp (.cv x) (.cv z)))))
      p0017 p0020
  have p0022 := @g_unex (.cv y) (.cv z) p0013 p0014
  have p0023 := @g_mucnc (.cv x) (syn_cun (.cv y) (.cv z)) p0003 p0022
  have p0024 := @g_xpundi (.cv x) (.cv y) (.cv z)
  have p0025 :=
    @g_nceqi (syn_cxp (.cv x) (syn_cun (.cv y) (.cv z)))
      (syn_cun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z))) p0024
  have p0026 :=
    @g_eqtri (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (syn_cun (.cv y) (.cv z))))
      (syn_cnc (syn_cxp (.cv x) (syn_cun (.cv y) (.cv z))))
      (syn_cnc (syn_cun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z)))) p0023 p0025
  have p0027 := @g_mucnc (.cv x) (.cv y) p0003 p0013
  have p0028 := @g_mucnc (.cv x) (.cv z) p0003 p0014
  have p0029 :=
    @g_addceq12i (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
      (syn_cnc (syn_cxp (.cv x) (.cv y)))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z)))
      (syn_cnc (syn_cxp (.cv x) (.cv z))) p0027 p0028
  have p0030 :=
    @g_n_3eqtr4g (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (syn_cnc (syn_cun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z))))
      (syn_cplc (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cnc (syn_cxp (.cv x) (.cv z))))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (syn_cun (.cv y) (.cv z))))
      (syn_cplc (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
        (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z))))
      p0021 p0026 p0029
  have p0031 :=
    @g_eqtr3d (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (syn_cun (.cv y) (.cv z))))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
      (syn_cplc (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
        (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z))))
      p0016 p0030
  have p0032 :=
    @g_oveq1 A (syn_cnc (.cv x)) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))) (syn_cmuc)
  have p0033 := @g_oveq1 A (syn_cnc (.cv x)) (syn_cnc (.cv y)) (syn_cmuc)
  have p0034 := @g_oveq1 A (syn_cnc (.cv x)) (syn_cnc (.cv z)) (syn_cmuc)
  have p0035 :=
    @g_addceq12d (.classEq A (syn_cnc (.cv x))) (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
      (syn_co A (syn_cmuc) (syn_cnc (.cv z)))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z))) p0033 p0034
  have p0036 :=
    @g_eqeq12d (.classEq A (syn_cnc (.cv x)))
      (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
      (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z))))
      (syn_cplc (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
        (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z))))
      p0032 p0035
  have p0037 :=
    @g_syl5ibr (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
        (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
          (syn_co A (syn_cmuc) (syn_cnc (.cv z)))))
      (.classEq A (syn_cnc (.cv x)))
      (.classEq (syn_co (syn_cnc (.cv x)) (syn_cmuc)
          (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
        (syn_cplc (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
          (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z)))))
      p0031 p0036
  have p0038 :=
    @g_exlimiv (.classEq A (syn_cnc (.cv x)))
      (.imp (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
          (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
            (syn_co A (syn_cmuc) (syn_cnc (.cv z))))))
      x dv_cache_0010 p0037
  have p0039 :=
    @g_sylbi (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))
      (.imp (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
          (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
            (syn_co A (syn_cmuc) (syn_cnc (.cv z))))))
      p0012 p0038
  have p0040 :=
    @g_adantrd (.classMem A (syn_cncs)) (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
        (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
          (syn_co A (syn_cmuc) (syn_cnc (.cv z)))))
      (.classEq (.cv x) (syn_cun (.cv y) (.cv z))) p0039
  have p0041 := @g_addceq12 B C (syn_cnc (.cv y)) (syn_cnc (.cv z))
  have p0042 :=
    @g_oveq2d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z))))
      (syn_cplc B C) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))) A (syn_cmuc) p0041
  have p0043 := @g_oveq2 B (syn_cnc (.cv y)) A (syn_cmuc)
  have p0044 :=
    @g_adantr (.classEq B (syn_cnc (.cv y)))
      (.classEq (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) (syn_cnc (.cv y))))
      (.classEq C (syn_cnc (.cv z))) p0043
  have p0045 := @g_oveq2 C (syn_cnc (.cv z)) A (syn_cmuc)
  have p0046 :=
    @g_adantl (.classEq C (syn_cnc (.cv z)))
      (.classEq (syn_co A (syn_cmuc) C) (syn_co A (syn_cmuc) (syn_cnc (.cv z))))
      (.classEq B (syn_cnc (.cv y))) p0045
  have p0047 :=
    @g_addceq12d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z))))
      (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
      (syn_co A (syn_cmuc) C) (syn_co A (syn_cmuc) (syn_cnc (.cv z))) p0044 p0046
  have p0048 :=
    @g_eqeq12d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z))))
      (syn_co A (syn_cmuc) (syn_cplc B C))
      (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
      (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))
      (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z))))
      p0042 p0047
  have p0049 :=
    @g_imbi2d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z))))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
        (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
        (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
          (syn_co A (syn_cmuc) (syn_cnc (.cv z)))))
      (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
      p0048
  have p0050 :=
    @g_syl5ibrcom (.classMem A (syn_cncs))
      (.imp (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
        (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
          (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))))
      (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z))))
      (.imp (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
        (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))))
          (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y)))
            (syn_co A (syn_cmuc) (syn_cnc (.cv z))))))
      p0040 p0049
  have p0051 :=
    @g_n_3ad2ant1 (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (.imp (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (.imp
          (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
          (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
            (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))))
      (.classMem C (syn_cncs)) p0050
  have p0052 :=
    @g_sylbird
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wa (.classMem (.cv y) B) (.classMem (.cv z) C))
      (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z))))
      (.imp (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
        (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
          (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))))
      p0011 p0051
  have p0053 :=
    @g_rexlimdvv
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
        (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))
      y z B C dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0008 p0052
  have p0054 :=
    @g_syl5bi (.classMem (.cv x) (syn_cplc B C))
      (syn_wrex y B (syn_wrex z C (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))))
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
        (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))
      p0007 p0053
  have p0055 :=
    @g_syl5 (.classEq (syn_cplc B C) (syn_cnc (.cv x))) (.classMem (.cv x) (syn_cplc B C))
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
        (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))
      p0006 p0054
  have p0056 :=
    @g_exlimdv
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (.classEq (syn_cplc B C) (syn_cnc (.cv x)))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
        (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))
      x dv_cache_0015 dv_cache_0016 p0055
  have p0057 :=
    @g_syl5bi (.classMem (syn_cplc B C) (syn_cncs))
      (syn_wex x (.classEq (syn_cplc B C) (syn_cnc (.cv x))))
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
        (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))
      p0002 p0056
  have p0058 :=
    @g_mpd
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (.classMem (syn_cplc B C) (syn_cncs))
      (.classEq (syn_co A (syn_cmuc) (syn_cplc B C))
        (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))
      p0001 p0057
  exact p0058

@[expose]
noncomputable def g_addcdir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
        (.classEq (syn_co (syn_cplc A B) (syn_cmuc) C)
          (syn_cplc (syn_co A (syn_cmuc) C) (syn_co B (syn_cmuc) C)))) :=
  by
  have p0000 := @g_addcdi C A B
  have p0001 :=
    @g_n_3coml (.classMem C (syn_cncs)) (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (.classEq (syn_co C (syn_cmuc) (syn_cplc A B))
        (syn_cplc (syn_co C (syn_cmuc) A) (syn_co C (syn_cmuc) B)))
      p0000
  have p0002 := @g_ncaddccl A B
  have p0003 :=
    @g_n_3adant3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (.classMem (syn_cplc A B) (syn_cncs)) (.classMem C (syn_cncs)) p0002
  have p0004 :=
    @g_simp3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
  have p0005 := @g_muccom (syn_cplc A B) C
  have p0006 :=
    @g_syl2anc
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (.classMem (syn_cplc A B) (syn_cncs)) (.classMem C (syn_cncs))
      (.classEq (syn_co (syn_cplc A B) (syn_cmuc) C) (syn_co C (syn_cmuc) (syn_cplc A B)))
      p0003 p0004 p0005
  have p0007 := @g_muccom A C
  have p0008 :=
    @g_n_3adant2 (.classMem A (syn_cncs)) (.classMem C (syn_cncs))
      (.classEq (syn_co A (syn_cmuc) C) (syn_co C (syn_cmuc) A)) (.classMem B (syn_cncs))
      p0007
  have p0009 := @g_muccom B C
  have p0010 :=
    @g_n_3adant1 (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
      (.classEq (syn_co B (syn_cmuc) C) (syn_co C (syn_cmuc) B)) (.classMem A (syn_cncs))
      p0009
  have p0011 :=
    @g_addceq12d
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_co A (syn_cmuc) C) (syn_co C (syn_cmuc) A) (syn_co B (syn_cmuc) C)
      (syn_co C (syn_cmuc) B) p0008 p0010
  have p0012 :=
    @g_n_3eqtr4d
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_co C (syn_cmuc) (syn_cplc A B))
      (syn_cplc (syn_co C (syn_cmuc) A) (syn_co C (syn_cmuc) B))
      (syn_co (syn_cplc A B) (syn_cmuc) C)
      (syn_cplc (syn_co A (syn_cmuc) C) (syn_co B (syn_cmuc) C)) p0001 p0006 p0011
  exact p0012

@[expose]
noncomputable def g_lemuc1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
            (.classMem C (syn_cncs))) (syn_wbr A (syn_clec) B))
        (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C))) :=
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
    q ∉ ((syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C))).fv :=
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
    q ∉ ((syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))).fv :=
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
  have p0000 := @g_dflec2 A B q dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_3adant3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (syn_wb (syn_wbr A (syn_clec) B)
        (syn_wrex q (syn_cncs) (.classEq B (syn_cplc A (.cv q)))))
      (.classMem C (syn_cncs)) p0000
  have p0002 := @g_muccl A C
  have p0003 :=
    @g_adantr (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))
      (.classMem (syn_co A (syn_cmuc) C) (syn_cncs)) (.classMem (.cv q) (syn_cncs)) p0002
  have p0004 := @g_muccl (.cv q) C
  have p0005 :=
    @g_ancoms (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs))
      (.classMem (syn_co (.cv q) (syn_cmuc) C) (syn_cncs)) p0004
  have p0006 :=
    @g_adantll (.classMem C (syn_cncs)) (.classMem (.cv q) (syn_cncs))
      (.classMem (syn_co (.cv q) (syn_cmuc) C) (syn_cncs)) (.classMem A (syn_cncs)) p0005
  have p0007 := @g_addlecncs (syn_co A (syn_cmuc) C) (syn_co (.cv q) (syn_cmuc) C)
  have p0008 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (.classMem (syn_co A (syn_cmuc) C) (syn_cncs))
      (.classMem (syn_co (.cv q) (syn_cmuc) C) (syn_cncs))
      (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec)
        (syn_cplc (syn_co A (syn_cmuc) C) (syn_co (.cv q) (syn_cmuc) C)))
      p0003 p0006 p0007
  have p0009 :=
    @g_simpll (.classMem A (syn_cncs)) (.classMem C (syn_cncs))
      (.classMem (.cv q) (syn_cncs))
  have p0010 :=
    @g_simpr (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))
      (.classMem (.cv q) (syn_cncs))
  have p0011 :=
    @g_simplr (.classMem A (syn_cncs)) (.classMem C (syn_cncs))
      (.classMem (.cv q) (syn_cncs))
  have p0012 := @g_addcdir A (.cv q) C
  have p0013 :=
    @g_syl3anc
      (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (.classMem A (syn_cncs)) (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs))
      (.classEq (syn_co (syn_cplc A (.cv q)) (syn_cmuc) C)
        (syn_cplc (syn_co A (syn_cmuc) C) (syn_co (.cv q) (syn_cmuc) C)))
      p0009 p0010 p0011 p0012
  have p0014 :=
    @g_breqtrrd
      (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (syn_co A (syn_cmuc) C)
      (syn_cplc (syn_co A (syn_cmuc) C) (syn_co (.cv q) (syn_cmuc) C))
      (syn_co (syn_cplc A (.cv q)) (syn_cmuc) C) (syn_clec) p0008 p0013
  have p0015 := @g_oveq1 B (syn_cplc A (.cv q)) C (syn_cmuc)
  have p0016 :=
    @g_breq2d (.classEq B (syn_cplc A (.cv q))) (syn_co B (syn_cmuc) C)
      (syn_co (syn_cplc A (.cv q)) (syn_cmuc) C) (syn_co A (syn_cmuc) C) (syn_clec) p0015
  have p0017 :=
    @g_syl5ibrcom
      (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))
        (.classMem (.cv q) (syn_cncs)))
      (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C))
      (.classEq B (syn_cplc A (.cv q)))
      (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co (syn_cplc A (.cv q)) (syn_cmuc) C))
      p0014 p0016
  have p0018 :=
    @g_rexlimdva (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))
      (.classEq B (syn_cplc A (.cv q)))
      (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C)) q (syn_cncs)
      dv_cache_0003 dv_cache_0004 p0017
  have p0019 :=
    @g_n_3adant2 (.classMem A (syn_cncs)) (.classMem C (syn_cncs))
      (.imp (syn_wrex q (syn_cncs) (.classEq B (syn_cplc A (.cv q))))
        (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C)))
      (.classMem B (syn_cncs)) p0018
  have p0020 :=
    @g_sylbid
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wbr A (syn_clec) B) (syn_wrex q (syn_cncs) (.classEq B (syn_cplc A (.cv q))))
      (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C)) p0001 p0019
  have p0021 :=
    @g_imp
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wbr A (syn_clec) B)
      (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C)) p0020
  exact p0021

@[expose]
noncomputable def g_lemuc2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
            (.classMem C (syn_cncs))) (syn_wbr B (syn_clec) C))
        (syn_wbr (syn_co A (syn_cmuc) B) (syn_clec) (syn_co A (syn_cmuc) C))) :=
  by
  have p0000 :=
    @g_n_3anrot (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
  have p0001 := @g_lemuc1 B C A
  have p0002 :=
    @g_sylanb
      (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_w3a (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (.classMem A (syn_cncs)))
      (syn_wbr B (syn_clec) C)
      (syn_wbr (syn_co B (syn_cmuc) A) (syn_clec) (syn_co C (syn_cmuc) A)) p0000 p0001
  have p0003 :=
    @g_simpl1 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
      (syn_wbr B (syn_clec) C)
  have p0004 :=
    @g_simpl2 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
      (syn_wbr B (syn_clec) C)
  have p0005 := @g_muccom A B
  have p0006 :=
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs))) (syn_wbr B (syn_clec) C))
      (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A)) p0003 p0004 p0005
  have p0007 :=
    @g_simpl3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
      (syn_wbr B (syn_clec) C)
  have p0008 := @g_muccom A C
  have p0009 :=
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs))) (syn_wbr B (syn_clec) C))
      (.classMem A (syn_cncs)) (.classMem C (syn_cncs))
      (.classEq (syn_co A (syn_cmuc) C) (syn_co C (syn_cmuc) A)) p0003 p0007 p0008
  have p0010 :=
    @g_n_3brtr4d
      (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
          (.classMem C (syn_cncs))) (syn_wbr B (syn_clec) C))
      (syn_co B (syn_cmuc) A) (syn_co C (syn_cmuc) A) (syn_co A (syn_cmuc) B)
      (syn_co A (syn_cmuc) C) (syn_clec) p0002 p0006 p0009
  exact p0010

@[expose]
noncomputable def g_n_0lt1c : Nominal.NPrf (syn_wbr (syn_c0c) (syn_cltc) (syn_c1c)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @g_df0c2
  have p0001 := @g_n_0ss (syn_csn (.cv x))
  have p0002 := @g_n_0ex
  have p0003 := @g_snex (.cv x)
  have p0004 := @g_nclec (syn_c0) (syn_csn (.cv x)) p0002 p0003
  have p0005 := Nominal.mp p0001 p0004
  have p0006 :=
    @g_eqbrtri (syn_c0c) (syn_cnc (syn_c0)) (syn_cnc (syn_csn (.cv x))) (syn_clec) p0000
      p0005
  have p0007 := @g_vex x
  have p0008 := @g_snnz (.cv x) p0007
  have p0009 := (Nominal.biimpRefl (syn_wne (syn_csn (.cv x)) (syn_c0)))
  have p0010 :=
    @g_mpbi (syn_wne (syn_csn (.cv x)) (syn_c0))
      (.neg (.classEq (syn_csn (.cv x)) (syn_c0))) p0008 p0009
  have p0011 := @g_ncid (syn_csn (.cv x)) p0003
  have p0012 := @g_eleq2 (syn_c0c) (syn_cnc (syn_csn (.cv x))) (syn_csn (.cv x))
  have p0013 :=
    @g_mpbiri (.classEq (syn_c0c) (syn_cnc (syn_csn (.cv x))))
      (.classMem (syn_csn (.cv x)) (syn_c0c))
      (.classMem (syn_csn (.cv x)) (syn_cnc (syn_csn (.cv x)))) p0011 p0012
  have p0014 := @g_el0c (syn_csn (.cv x))
  have p0015 :=
    @g_sylib (.classEq (syn_c0c) (syn_cnc (syn_csn (.cv x))))
      (.classMem (syn_csn (.cv x)) (syn_c0c)) (.classEq (syn_csn (.cv x)) (syn_c0)) p0013
      p0014
  have p0016 :=
    @g_mto (.classEq (syn_c0c) (syn_cnc (syn_csn (.cv x))))
      (.classEq (syn_csn (.cv x)) (syn_c0)) p0010 p0015
  have p0017 := (Nominal.biimpRefl (syn_wne (syn_c0c) (syn_cnc (syn_csn (.cv x)))))
  have p0018 :=
    @g_mpbir (syn_wne (syn_c0c) (syn_cnc (syn_csn (.cv x))))
      (.neg (.classEq (syn_c0c) (syn_cnc (syn_csn (.cv x))))) p0016 p0017
  have p0019 := @g_brltc (syn_c0c) (syn_cnc (syn_csn (.cv x)))
  have p0020 :=
    @g_mpbir2an (syn_wbr (syn_c0c) (syn_cltc) (syn_cnc (syn_csn (.cv x))))
      (syn_wbr (syn_c0c) (syn_clec) (syn_cnc (syn_csn (.cv x))))
      (syn_wne (syn_c0c) (syn_cnc (syn_csn (.cv x)))) p0006 p0018 p0019
  have p0021 := @g_df1c3 (.cv x) p0007
  have p0022 :=
    @g_breqtrri (syn_c0c) (syn_cnc (syn_csn (.cv x))) (syn_c1c) (syn_cltc) p0020 p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end
