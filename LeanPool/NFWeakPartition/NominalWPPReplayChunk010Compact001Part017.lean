/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block006

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part017. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tfinnn`. -/
@[expose]
noncomputable def gTfinnn (x : Var) (A : Class) (N : Class) (a : Var) (dv_A_a : a ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (_dv_N_a : a ∉ N.fv) (_dv_N_x : x ∉ N.fv) (dv_a_x : a ≠ x) :
    Nominal.NPrf
      (.imp (synW3a (.classMem N (synCnnc)) (synWss A (synCnnc)) (.classMem A N))
        (.classMem (.cab a (synWrex x A (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin N))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ A.fv ∪ N.fv ∪ ({ a } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let k : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let w : Var := freshVar proofSupport 5
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
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_a : y ≠ a := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_k_ne_x : k ≠ x := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_k : x ≠ k := Ne.symm fresh_k_ne_x
  have fresh_k_ne_a : k ≠ a := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_a : b ≠ a := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_b : a ≠ b := Ne.symm fresh_b_ne_a
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_a : w ≠ a := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_w : a ≠ w := Ne.symm fresh_w_ne_a
  have fresh_y_ne_n : y ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_y_ne_k : y ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_k_ne_y : k ≠ y := Ne.symm fresh_y_ne_k
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_n_ne_k : n ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_k_ne_n : k ≠ n := Ne.symm fresh_n_ne_k
  have fresh_n_ne_z : n ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_z : k ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_k : z ≠ k := Ne.symm fresh_k_ne_z
  have fresh_k_ne_b : k ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_k : b ≠ k := Ne.symm fresh_k_ne_b
  have fresh_k_ne_w : k ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_w_ne_k : w ≠ k := Ne.symm fresh_k_ne_w
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_b_ne_w : b ≠ w :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have dv_cache_0001 : a ≠ n := by exact (show a ≠ n from (by exact fresh_a_ne_n))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact dv_a_x))
  have dv_cache_0003 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : n ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0005 : n ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show n ≠ y from (by exact fresh_n_ne_y))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : y ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_n, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synC0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Wff.classEq (.cv y) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0013 :
    y ∉
      ((Wff.imp (synWss (synC0) (synCnnc)) (.all a
            (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x)))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_k, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((synCplc (.cv k) (synC1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((synCplc (.cv k) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    z ∉
      ((Wff.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (synCplc (.cv k) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_a,
          fresh_z_ne_x, fresh_z_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0020 :
    y ∉
      ((Wff.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (synCplc (.cv k) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_a,
          fresh_y_ne_x, fresh_y_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0021 : y ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_N, not_false_eq_true])
  have dv_cache_0022 : b ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0023 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0024 : b ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_k, not_false_eq_true])
  have dv_cache_0025 : b ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show b ≠ w from (by exact fresh_b_ne_w))
  have dv_cache_0026 : x ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_b, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((Wff.objEq y b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_b, or_false, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0029 :
    y ∉
      ((Wff.imp (synWss (.cv b) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_b, fresh_y_ne_a,
          fresh_y_ne_x, fresh_y_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0030 :
    x ∉
      ((synWa (synWa (.classMem (.cv k) (synCnnc))
            (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
          (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_k, fresh_x_ne_b,
          fresh_x_ne_w, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0031 : x ∉ ((Wff.classEq (.cv a) (synCtfin (.cv w)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_x), fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0032 : a ∉ ((synCtfin (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_w,
          not_false_eq_true])
  have dv_cache_0033 :
    a ∉ ((synWrex x (.cv b) (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_w, dv_a_x,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0034 : x ∉ ((synCun (.cv b) (synCsn (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_b, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0035 :
    a ∉ ((Wff.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_b, fresh_a_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0036 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0037 : w ∉ ((Class.cv k)).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_k, not_false_eq_true])
  have dv_cache_0038 :
    b ∉
      ((Wff.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCplc (synCtfin (.cv k)) (synC1c))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_a,
          fresh_b_ne_x, fresh_b_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0039 :
    w ∉
      ((Wff.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCplc (synCtfin (.cv k)) (synC1c))))).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_a,
          fresh_w_ne_x, fresh_w_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0040 :
    b ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
            (.imp (synWss (.cv y) (synCnnc)) (.classMem
                (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv k))))))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_k, fresh_b_ne_y,
          fresh_b_ne_a, fresh_b_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0041 :
    w ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
            (.imp (synWss (.cv y) (synCnnc)) (.classMem
                (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv k))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_k, fresh_w_ne_y,
          fresh_w_ne_a, fresh_w_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0042 :
    z ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
            (.imp (synWss (.cv y) (synCnnc)) (.classMem
                (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv k))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_k, fresh_z_ne_y,
          fresh_z_ne_a, fresh_z_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0043 : n ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0044 :
    n ∉
      ((synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_y,
          fresh_n_ne_a, fresh_n_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0045 :
    k ∉
      ((synWral y (.cv n) (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_n, fresh_k_ne_y,
          fresh_k_ne_a, fresh_k_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0046 :
    n ∉
      ((Wff.imp (synWss (synC0) (synCnnc)) (.all a
            (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0047 :
    n ∉
      ((synWral y N (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin N))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_not_N, fresh_n_ne_y,
          fresh_n_ne_a, fresh_n_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0048 :
    n ∉
      ((synWral z (synCplc (.cv k) (synC1c)) (.imp (synWss (.cv z) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (synCplc (.cv k) (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_z,
          fresh_n_ne_a, fresh_n_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0049 : n ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact (show n ≠ k from (by exact fresh_n_ne_k))
  have dv_cache_0050 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0051 : a ∉ ((Wff.classEq (.cv y) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, dv_A_a, or_false, not_false_eq_true])
  have dv_cache_0052 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0053 :
    y ∉
      ((Wff.imp (synWss A (synCnnc))
          (.classMem (.cab a (synWrex x A (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin N)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_a,
          fresh_y_ne_x, fresh_y_not_N, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @gTfinnnlem1 x y n a dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @gTfineq (.cv n) (synC0c)
  have p0002 := @gTfin0c
  have p0003 :=
    @gSyl6eq (.classEq (.cv n) (synC0c)) (synCtfin (.cv n)) (synCtfin (synC0c))
      (synC0c) p0001 p0002
  have p0004 :=
    @gEleq2d (.classEq (.cv n) (synC0c)) (synCtfin (.cv n)) (synC0c)
      (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) p0003
  have p0005 :=
    @gImbi2d (.classEq (.cv n) (synC0c))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv n)))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) (synC0c))
      (synWss (.cv y) (synCnnc)) p0004
  have p0006 :=
    @gRaleqbi1dv
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv n))))
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synC0c)))
      y (.cv n) (synC0c) dv_cache_0007 dv_cache_0008 p0005
  have p0007 :=
    (Nominal.biimpRefl (synWral y (synC0c) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synC0c)))))
  have p0008 := @gEl0c (.cv y)
  have p0009 :=
    @gEl0c (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
  have p0010 := @gAb0 (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))) a
  have p0011 :=
    @gBitri
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) (synC0c))
      (.classEq (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) (synC0))
      (.all a (.neg (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))) p0009
      p0010
  have p0012 :=
    @gImbi2i
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) (synC0c))
      (.all a (.neg (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))
      (synWss (.cv y) (synCnnc)) p0011
  have p0013 :=
    @gImbi12i (.classMem (.cv y) (synC0c)) (.classEq (.cv y) (synC0))
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synC0c)))
      (.imp (synWss (.cv y) (synCnnc))
        (.all a (.neg (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))))
      p0008 p0012
  have p0014 :=
    @gAlbii
      (.imp (.classMem (.cv y) (synC0c)) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synC0c))))
      (.imp (.classEq (.cv y) (synC0)) (.imp (synWss (.cv y) (synCnnc))
          (.all a (.neg (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))))
      y p0013
  have p0015 := @gN0ex
  have p0016 := @gSseq1 (.cv y) (synC0) (synCnnc)
  have p0017 :=
    @gRexeq (.classEq (.cv a) (synCtfin (.cv x))) x (.cv y) (synC0) dv_cache_0009
      dv_cache_0010
  have p0018 :=
    @gNotbid (.classEq (.cv y) (synC0))
      (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x)))) p0017
  have p0019 :=
    @gAlbidv (.classEq (.cv y) (synC0))
      (.neg (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
      (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x))))) a dv_cache_0011
      p0018
  have p0020 :=
    @gImbi12d (.classEq (.cv y) (synC0)) (synWss (.cv y) (synCnnc))
      (synWss (synC0) (synCnnc))
      (.all a (.neg (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))
      (.all a (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x)))))) p0016
      p0019
  have p0021 :=
    @gCeqsalv
      (.imp (synWss (.cv y) (synCnnc))
        (.all a (.neg (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))))
      (.imp (synWss (synC0) (synCnnc))
        (.all a (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x)))))))
      y (synC0) dv_cache_0012 dv_cache_0013 p0015 p0020
  have p0022 :=
    @gN3bitri
      (synWral y (synC0c) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synC0c))))
      (.all y (.imp (.classMem (.cv y) (synC0c)) (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) (synC0c)))))
      (.all y (.imp (.classEq (.cv y) (synC0)) (.imp (synWss (.cv y) (synCnnc))
            (.all a (.neg (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))))))
      (.imp (synWss (synC0) (synCnnc))
        (.all a (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x)))))))
      p0007 p0014 p0021
  have p0023 :=
    @gSyl6bb (.classEq (.cv n) (synC0c))
      (synWral y (.cv n) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv n)))))
      (synWral y (synC0c) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synC0c))))
      (.imp (synWss (synC0) (synCnnc))
        (.all a (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x)))))))
      p0006 p0022
  have p0024 := @gTfineq (.cv n) (.cv k)
  have p0025_e00_recanon :
    Nominal.NPrf (.imp (.objEq n k) (.classEq (synCtfin (.cv n)) (synCtfin (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl synCnin
          synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0025 :=
    @gEleq2d (.objEq n k) (synCtfin (.cv n)) (synCtfin (.cv k))
      (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
      p0025_e00_recanon
  have p0026 :=
    @gImbi2d (.objEq n k)
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv n)))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv k)))
      (synWss (.cv y) (synCnnc)) p0025
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv n) (.cv k)) (synWb (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv n)))) (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa synCnnc
          synCint synWrex synWex synCtfin synCif synWo synC0 synCdif synCvv
          synCio synCuni synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @gRaleqbi1dv
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv n))))
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv k))))
      y (.cv n) (.cv k) dv_cache_0007 dv_cache_0014 p0027_e00_recanon
  have p0028 := @gTfineq (.cv n) (synCplc (.cv k) (synC1c))
  have p0029 :=
    @gEleq2d (.classEq (.cv n) (synCplc (.cv k) (synC1c))) (synCtfin (.cv n))
      (synCtfin (synCplc (.cv k) (synC1c)))
      (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) p0028
  have p0030 :=
    @gImbi2d (.classEq (.cv n) (synCplc (.cv k) (synC1c)))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv n)))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (synCplc (.cv k) (synC1c))))
      (synWss (.cv y) (synCnnc)) p0029
  have p0031 :=
    @gRaleqbi1dv
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv n))))
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (synCplc (.cv k) (synC1c)))))
      y (.cv n) (synCplc (.cv k) (synC1c)) dv_cache_0007 dv_cache_0015 p0030
  have p0032 := @gSseq1 (.cv y) (.cv z) (synCnnc)
  have p0033 :=
    @gRexeq (.classEq (.cv a) (synCtfin (.cv x))) x (.cv y) (.cv z) dv_cache_0009
      dv_cache_0016
  have p0034_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (synWb (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))
          (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCtfin, synCif, synWo, synC0,
          synCdif, synCin, synCcompl, synCnin, synWnan, synCvv, synCio, synCuni,
          synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @gAbbidv (.objEq y z) (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))) a dv_cache_0017
      p0034_e00_recanon
  have p0035 :=
    @gEleq1d (.objEq y z)
      (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
      (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCtfin (synCplc (.cv k) (synC1c))) p0034
  have p0036_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (synWb (synWss (.cv y) (synCnnc)) (synWss (.cv z) (synCnnc)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa synCnnc
          synCint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0036 :=
    @gImbi12d (.objEq y z) (synWss (.cv y) (synCnnc)) (synWss (.cv z) (synCnnc))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (synCplc (.cv k) (synC1c))))
      (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (synCplc (.cv k) (synC1c))))
      p0036_e00_recanon p0035
  have p0037 :=
    @gCbvralv
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (synCplc (.cv k) (synC1c)))))
      (.imp (synWss (.cv z) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (synCplc (.cv k) (synC1c)))))
      y z (synCplc (.cv k) (synC1c)) dv_cache_0015 dv_cache_0018 dv_cache_0019
      dv_cache_0020 p0036
  have p0038 :=
    @gSyl6bb (.classEq (.cv n) (synCplc (.cv k) (synC1c)))
      (synWral y (.cv n) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv n)))))
      (synWral y (synCplc (.cv k) (synC1c)) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (synCplc (.cv k) (synC1c))))))
      (synWral z (synCplc (.cv k) (synC1c)) (.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (synCplc (.cv k) (synC1c))))))
      p0031 p0037
  have p0039 := @gTfineq (.cv n) N
  have p0040 :=
    @gEleq2d (.classEq (.cv n) N) (synCtfin (.cv n)) (synCtfin N)
      (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) p0039
  have p0041 :=
    @gImbi2d (.classEq (.cv n) N)
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv n)))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin N))
      (synWss (.cv y) (synCnnc)) p0040
  have p0042 :=
    @gRaleqbi1dv
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv n))))
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin N)))
      y (.cv n) N dv_cache_0007 dv_cache_0021 p0041
  have p0043 := @gRex0 (.classEq (.cv a) (synCtfin (.cv x))) x
  have p0044 := Nominal.gen p0043 a
  have p0045 :=
    @gA1i (.all a (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x))))))
      (synWss (synC0) (synCnnc)) p0044
  have p0046 :=
    @gElsuc w (.cv z) (.cv k) b dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
  have p0047 := @gSseq1 (.cv y) (.cv b) (synCnnc)
  have p0048 :=
    @gRexeq (.classEq (.cv a) (synCtfin (.cv x))) x (.cv y) (.cv b) dv_cache_0009
      dv_cache_0026
  have p0049_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y b) (synWb (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))
          (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCtfin, synCif, synWo, synC0,
          synCdif, synCin, synCcompl, synCnin, synWnan, synCvv, synCio, synCuni,
          synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0048
  have p0049 :=
    @gAbbidv (.objEq y b) (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))) a dv_cache_0027
      p0049_e00_recanon
  have p0050 :=
    @gEleq1d (.objEq y b)
      (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
      (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCtfin (.cv k)) p0049
  have p0051_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y b) (synWb (synWss (.cv y) (synCnnc)) (synWss (.cv b) (synCnnc)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa synCnnc
          synCint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0047
  have p0051 :=
    @gImbi12d (.objEq y b) (synWss (.cv y) (synCnnc)) (synWss (.cv b) (synCnnc))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv k)))
      (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv k)))
      p0051_e00_recanon p0050
  have p0052_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv b)) (synWb (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k)))) (.imp (synWss (.cv b) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa synCnnc
          synCint synWrex synWex synCtfin synCif synWo synC0 synCdif synCvv
          synCio synCuni synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0051
  have p0052 :=
    @gRspcv
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv k))))
      (.imp (synWss (.cv b) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv k))))
      y (.cv b) (.cv k) dv_cache_0028 dv_cache_0014 dv_cache_0029 p0052_e00_recanon
  have p0053_e00_recanon :
    Nominal.NPrf
      (.imp (.objMem b k) (.imp (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc))
              (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv k))))) (.imp (synWss (.cv b) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWral synWss synCin synCcompl synCnin synWnan synWa synCnnc
          synCint synWrex synWex synCtfin synCif synWo synC0 synCdif synCvv
          synCio synCuni synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0052
  have p0053 :=
    @gAd2antrl (.objMem b k)
      (.imp (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k))))) (.imp (synWss (.cv b) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k)))))
      (.classMem (.cv k) (synCnnc)) (.classMem (.cv w) (synCcompl (.cv b)))
      p0053_e00_recanon
  have p0054 :=
    @gSimprl
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))
  have p0055 :=
    @gSimp3
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
      (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv k)))
  have p0056 :=
    @gSimplrr (.classMem (.cv k) (synCnnc)) (.objMem b k)
      (.classMem (.cv w) (synCcompl (.cv b)))
      (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
  have p0057 := @gVex w
  have p0058 := @gElcompl (.cv w) (.cv b) p0057
  have p0059_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv w) (synCcompl (.cv b))) (.neg (.objMem w b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @gSylib
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (.classMem (.cv w) (synCcompl (.cv b))) (.neg (.objMem w b)) p0056
      p0059_e01_recanon
  have p0060 := @gElequ1 w x b
  have p0061 := @gNotbid (.objEq w x) (.objMem w b) (.objMem x b) p0060
  have p0062 :=
    @gSyl5ibcom
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (.neg (.objMem w b)) (.objEq w x) (.neg (.objMem x b)) p0059 p0061
  have p0063 :=
    @gCon2d
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (.objEq w x) (.objMem x b) p0062
  have p0064 :=
    @gImp
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (.objMem x b) (.neg (.objEq w x)) p0063
  have p0065 :=
    @gSimpll
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (.objMem x b) (.classEq (synCtfin (.cv w)) (synCtfin (.cv x)))
  have p0066 :=
    @gSimprr
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))
  have p0067 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv k) (synCnnc))
              (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
            (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))) (.objMem x b))
        (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))))
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (.classMem (.cv w) (synCnnc)) p0065 p0066
  have p0068 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv k) (synCnnc))
              (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
            (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))) (.objMem x b))
        (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))))
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (synWss (.cv b) (synCnnc)) p0065 p0054
  have p0069 :=
    @gSimplr
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (.objMem x b) (.classEq (synCtfin (.cv w)) (synCtfin (.cv x)))
  have p0070_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWa (.classMem (.cv k) (synCnnc))
                (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
              (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
            (.objMem x b)) (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))))
        (.classMem (.cv x) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCtfin synCif synWo synC0 synCdif synCin synCcompl synCnin
          synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _)
      p0069
  have p0070 :=
    @gSseldd
      (synWa (synWa (synWa (synWa (.classMem (.cv k) (synCnnc))
              (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
            (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))) (.objMem x b))
        (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))))
      (.cv b) (synCnnc) (.cv x) p0068 p0070_e01_recanon
  have p0071 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv k) (synCnnc))
            (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
          (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))) (.objMem x b))
      (.classEq (synCtfin (.cv w)) (synCtfin (.cv x)))
  have p0072 := @gTfin11 (.cv w) (.cv x)
  have p0073_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv w) (synCnnc)) (.classMem (.cv x) (synCnnc))
          (.classEq (synCtfin (.cv w)) (synCtfin (.cv x)))) (.objEq w x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synCtfin synCif synWo synC0 synCdif
          synCin synCcompl synCnin synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0072
  have p0073 :=
    @gSyl3anc
      (synWa (synWa (synWa (synWa (.classMem (.cv k) (synCnnc))
              (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
            (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))) (.objMem x b))
        (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))))
      (.classMem (.cv w) (synCnnc)) (.classMem (.cv x) (synCnnc))
      (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))) (.objEq w x) p0067 p0070 p0071
      p0073_e03_recanon
  have p0074 :=
    @gMtand
      (synWa (synWa (synWa (.classMem (.cv k) (synCnnc))
            (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
          (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))) (.objMem x b))
      (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))) (.objEq w x) p0064 p0073
  have p0075_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem (.cv k) (synCnnc))
              (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
            (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
          (.classMem (.cv x) (.cv b)))
        (.neg (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCtfin synCif synWo synC0 synCdif synCin synCcompl synCnin
          synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0074
  have p0075 :=
    @gNrexdv
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))) x (.cv b) dv_cache_0030
      p0075_e00_recanon
  have p0076 :=
    @gN3adant3
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
      (.neg (synWrex x (.cv b) (.classEq (synCtfin (.cv w)) (synCtfin (.cv x)))))
      (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv k)))
      p0075
  have p0077 := @gTfinex (.cv w)
  have p0078 := @gEqeq1 (.cv a) (synCtfin (.cv w)) (synCtfin (.cv x))
  have p0079 :=
    @gRexbidv (.classEq (.cv a) (synCtfin (.cv w)))
      (.classEq (.cv a) (synCtfin (.cv x)))
      (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))) x (.cv b) dv_cache_0031 p0078
  have p0080 :=
    @gElab (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (.cv b) (.classEq (synCtfin (.cv w)) (synCtfin (.cv x)))) a
      (synCtfin (.cv w)) dv_cache_0032 dv_cache_0033 p0077 p0079
  have p0081 :=
    @gSylnibr
      (synW3a (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
        (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv k))))
      (synWrex x (.cv b) (.classEq (synCtfin (.cv w)) (synCtfin (.cv x))))
      (.classMem (synCtfin (.cv w))
        (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x))))))
      p0076 p0080
  have p0082 :=
    @gElsuci (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCtfin (.cv k)) (synCtfin (.cv w)) p0077
  have p0083 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
        (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv k))))
      (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv k)))
      (.neg (.classMem (synCtfin (.cv w))
          (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))))
      (.classMem (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCtfin (.cv w)))) (synCplc (synCtfin (.cv k)) (synC1c)))
      p0055 p0081 p0082
  have p0084 :=
    @gN3expia
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
      (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv k)))
      (.classMem (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCtfin (.cv w)))) (synCplc (synCtfin (.cv k)) (synC1c)))
      p0083
  have p0085 :=
    @gEmbantd
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
        (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))))
      (synWss (.cv b) (synCnnc))
      (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (.cv k)))
      (.classMem (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCtfin (.cv w)))) (synCplc (synCtfin (.cv k)) (synC1c)))
      p0054 p0084
  have p0086 :=
    @gEx
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
      (.imp (.imp (synWss (.cv b) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k)))) (.classMem
          (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCtfin (.cv w)))) (synCplc (synCtfin (.cv k)) (synC1c))))
      p0085
  have p0087 :=
    @gCom23
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
      (.imp (synWss (.cv b) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv k))))
      (.classMem (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCtfin (.cv w)))) (synCplc (synCtfin (.cv k)) (synC1c)))
      p0086
  have p0088 := @gSseq1 (.cv z) (synCun (.cv b) (synCsn (.cv w))) (synCnnc)
  have p0089 := @gSnss (.cv w) (synCnnc) p0057
  have p0090 :=
    @gAnbi2i (.classMem (.cv w) (synCnnc)) (synWss (synCsn (.cv w)) (synCnnc))
      (synWss (.cv b) (synCnnc)) p0089
  have p0091 := @gUnss (.cv b) (synCsn (.cv w)) (synCnnc)
  have p0092 :=
    @gBitr2i (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
      (synWa (synWss (.cv b) (synCnnc)) (synWss (synCsn (.cv w)) (synCnnc)))
      (synWss (synCun (.cv b) (synCsn (.cv w))) (synCnnc)) p0090 p0091
  have p0093 :=
    @gSyl6bb (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
      (synWss (.cv z) (synCnnc))
      (synWss (synCun (.cv b) (synCsn (.cv w))) (synCnnc))
      (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))) p0088 p0092
  have p0094 :=
    @gRexeq (.classEq (.cv a) (synCtfin (.cv x))) x (.cv z)
      (synCun (.cv b) (synCsn (.cv w))) dv_cache_0016 dv_cache_0034
  have p0095 :=
    @gRexun (.classEq (.cv a) (synCtfin (.cv x))) x (.cv b) (synCsn (.cv w))
  have p0096 :=
    @gSyl6bb (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
      (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (synCun (.cv b) (synCsn (.cv w))) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWo (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x))))
        (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x)))))
      p0094 p0095
  have p0097 :=
    @gAbbidv (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
      (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWo (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x))))
        (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x)))))
      a dv_cache_0035 p0096
  have p0098 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn a
      (synCtfin (.cv w)) dv_cache_0032
  have p0099 := @gTfineq (.cv x) (.cv w)
  have p0100_e00_recanon :
    Nominal.NPrf (.imp (.objEq x w) (.classEq (synCtfin (.cv x)) (synCtfin (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl synCnin
          synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0099
  have p0100 :=
    @gEqeq2d (.objEq x w) (synCtfin (.cv x)) (synCtfin (.cv w)) (.cv a)
      p0100_e00_recanon
  have p0101_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv w)) (synWb (.classEq (.cv a) (synCtfin (.cv x)))
          (.classEq (.cv a) (synCtfin (.cv w))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl
          synCnin synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0100
  have p0101 :=
    @gRexsn (.classEq (.cv a) (synCtfin (.cv x))) (.classEq (.cv a) (synCtfin (.cv w)))
      x (.cv w) dv_cache_0036 dv_cache_0031 p0057 p0101_e01_recanon
  have p0102 :=
    @gAbbii (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x))))
      (.classEq (.cv a) (synCtfin (.cv w))) a p0101
  have p0103 :=
    @gEqtr4i (synCsn (synCtfin (.cv w)))
      (.cab a (.classEq (.cv a) (synCtfin (.cv w))))
      (.cab a (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x))))) p0098
      p0102
  have p0104 :=
    @gUneq2i (synCsn (synCtfin (.cv w)))
      (.cab a (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x)))))
      (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x))))) p0103
  have p0105 :=
    @gUnab (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x)))) a
  have p0106 :=
    @gEqtr2i
      (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCsn (synCtfin (.cv w))))
      (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (.cab a (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x))))))
      (.cab a (synWo (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x))))
          (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x))))))
      p0104 p0105
  have p0107 :=
    @gSyl6eq (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
      (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
      (.cab a (synWo (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x))))
          (synWrex x (synCsn (.cv w)) (.classEq (.cv a) (synCtfin (.cv x))))))
      (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCsn (synCtfin (.cv w))))
      p0097 p0106
  have p0108 :=
    @gEleq1d (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
      (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCsn (synCtfin (.cv w))))
      (synCplc (synCtfin (.cv k)) (synC1c)) p0107
  have p0109 :=
    @gImbi12d (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
      (synWss (.cv z) (synCnnc))
      (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc)))
      (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCplc (synCtfin (.cv k)) (synC1c)))
      (.classMem (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCtfin (.cv w)))) (synCplc (synCtfin (.cv k)) (synC1c)))
      p0093 p0108
  have p0110 :=
    @gBiimprcd (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
      (.imp (synWss (.cv z) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCplc (synCtfin (.cv k)) (synC1c))))
      (.imp (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))) (.classMem
          (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCtfin (.cv w)))) (synCplc (synCtfin (.cv k)) (synC1c))))
      p0109
  have p0111 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (.imp (synWss (.cv b) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv k))))
      (.imp (synWa (synWss (.cv b) (synCnnc)) (.classMem (.cv w) (synCnnc))) (.classMem
          (synCun (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCtfin (.cv w)))) (synCplc (synCtfin (.cv k)) (synC1c))))
      (.imp (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
        (.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCplc (synCtfin (.cv k)) (synC1c)))))
      p0087 p0110
  have p0112 :=
    @gSyld
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k)))))
      (.imp (synWss (.cv b) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv b) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (.cv k))))
      (.imp (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
        (.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCplc (synCtfin (.cv k)) (synC1c)))))
      p0053 p0111
  have p0113 :=
    @gImp
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b)))))
      (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k)))))
      (.imp (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
        (.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCplc (synCtfin (.cv k)) (synC1c)))))
      p0112
  have p0114 :=
    @gAn32s (.classMem (.cv k) (synCnnc))
      (synWa (.objMem b k) (.classMem (.cv w) (synCcompl (.cv b))))
      (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k)))))
      (.imp (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
        (.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCplc (synCtfin (.cv k)) (synC1c)))))
      p0113
  have p0115_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
              (.imp (synWss (.cv y) (synCnnc)) (.classMem
                  (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                  (synCtfin (.cv k))))))
          (synWa (.classMem (.cv b) (.cv k)) (.classMem (.cv w) (synCcompl (.cv b)))))
        (.imp (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
          (.imp (synWss (.cv z) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCplc (synCtfin (.cv k)) (synC1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCun synCnin synWnan synCcompl synCsn synWss synCin
          synCnnc synCint synWrex synWex synCtfin synCif synWo synC0 synCdif
          synCvv synCio synCuni synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0114
  have p0115 :=
    @gRexlimdvva
      (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
          (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k))))))
      (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))
      (.imp (synWss (.cv z) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCplc (synCtfin (.cv k)) (synC1c))))
      b w (.cv k) (synCcompl (.cv b)) dv_cache_0037 dv_cache_0038 dv_cache_0039
      dv_cache_0040 dv_cache_0041 dv_cache_0025 p0115_e00_recanon
  have p0116 :=
    @gSyl5bi (.classMem (.cv z) (synCplc (.cv k) (synC1c)))
      (synWrex b (.cv k) (synWrex w (synCcompl (.cv b))
          (.classEq (.cv z) (synCun (.cv b) (synCsn (.cv w))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
          (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k))))))
      (.imp (synWss (.cv z) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCplc (synCtfin (.cv k)) (synC1c))))
      p0046 p0115
  have p0117 :=
    @gImp32
      (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
          (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k))))))
      (.classMem (.cv z) (synCplc (.cv k) (synC1c))) (synWss (.cv z) (synCnnc))
      (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCplc (synCtfin (.cv k)) (synC1c)))
      p0116
  have p0118 :=
    @gSimpll (.classMem (.cv k) (synCnnc))
      (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k)))))
      (synWa (.classMem (.cv z) (synCplc (.cv k) (synC1c))) (synWss (.cv z) (synCnnc)))
  have p0119 := @gNe0i (synCplc (.cv k) (synC1c)) (.cv z)
  have p0120 :=
    @gAd2antrl (.classMem (.cv z) (synCplc (.cv k) (synC1c)))
      (synWne (synCplc (.cv k) (synC1c)) (synC0))
      (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
          (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k))))))
      (synWss (.cv z) (synCnnc)) p0119
  have p0121 := @gTfinsuc (.cv k)
  have p0122 :=
    @gSyl2anc
      (synWa (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
            (.imp (synWss (.cv y) (synCnnc)) (.classMem
                (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv k)))))) (synWa (.classMem (.cv z) (synCplc (.cv k) (synC1c)))
          (synWss (.cv z) (synCnnc))))
      (.classMem (.cv k) (synCnnc)) (synWne (synCplc (.cv k) (synC1c)) (synC0))
      (.classEq (synCtfin (synCplc (.cv k) (synC1c)))
        (synCplc (synCtfin (.cv k)) (synC1c)))
      p0118 p0120 p0121
  have p0123 :=
    @gEleqtrrd
      (synWa (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
            (.imp (synWss (.cv y) (synCnnc)) (.classMem
                (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv k)))))) (synWa (.classMem (.cv z) (synCplc (.cv k) (synC1c)))
          (synWss (.cv z) (synCnnc))))
      (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCplc (synCtfin (.cv k)) (synC1c)) (synCtfin (synCplc (.cv k) (synC1c)))
      p0117 p0122
  have p0124 :=
    @gExpr
      (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
          (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k))))))
      (.classMem (.cv z) (synCplc (.cv k) (synC1c))) (synWss (.cv z) (synCnnc))
      (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (synCplc (.cv k) (synC1c))))
      p0123
  have p0125 :=
    @gRalrimiva
      (synWa (.classMem (.cv k) (synCnnc)) (synWral y (.cv k)
          (.imp (synWss (.cv y) (synCnnc)) (.classMem
              (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCtfin (.cv k))))))
      (.imp (synWss (.cv z) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin (synCplc (.cv k) (synC1c)))))
      z (synCplc (.cv k) (synC1c)) dv_cache_0042 p0124
  have p0126 :=
    @gEx (.classMem (.cv k) (synCnnc))
      (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k)))))
      (synWral z (synCplc (.cv k) (synC1c)) (.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (synCplc (.cv k) (synC1c))))))
      p0125
  have p0127_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n k) (synWb (synWral y (.cv n) (.imp (synWss (.cv y) (synCnnc))
              (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv n))))) (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc))
              (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv k))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWral synWss synCin synCcompl synCnin synWnan synWa
          synCnnc synCint synWrex synWex synCtfin synCif synWo synC0 synCdif
          synCvv synCio synCuni synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0127 :=
    @gFinds
      (synWral y (.cv n) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv n)))))
      (.imp (synWss (synC0) (synCnnc))
        (.all a (.neg (synWrex x (synC0) (.classEq (.cv a) (synCtfin (.cv x)))))))
      (synWral y (.cv k) (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (.cv k)))))
      (synWral z (synCplc (.cv k) (synC1c)) (.imp (synWss (.cv z) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv z) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin (synCplc (.cv k) (synC1c))))))
      (synWral y N (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin N))))
      n k N dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 p0000 p0023 p0127_e02_recanon p0038 p0042 p0045 p0126
  have p0128 := @gSseq1 (.cv y) A (synCnnc)
  have p0129 :=
    @gRexeq (.classEq (.cv a) (synCtfin (.cv x))) x (.cv y) A dv_cache_0009
      dv_cache_0050
  have p0130 :=
    @gAbbidv (.classEq (.cv y) A)
      (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x A (.classEq (.cv a) (synCtfin (.cv x)))) a dv_cache_0051 p0129
  have p0131 :=
    @gEleq1d (.classEq (.cv y) A)
      (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
      (.cab a (synWrex x A (.classEq (.cv a) (synCtfin (.cv x))))) (synCtfin N) p0130
  have p0132 :=
    @gImbi12d (.classEq (.cv y) A) (synWss (.cv y) (synCnnc)) (synWss A (synCnnc))
      (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin N))
      (.classMem (.cab a (synWrex x A (.classEq (.cv a) (synCtfin (.cv x))))) (synCtfin N))
      p0128 p0131
  have p0133 :=
    @gRspccv
      (.imp (synWss (.cv y) (synCnnc))
        (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin N)))
      (.imp (synWss A (synCnnc))
        (.classMem (.cab a (synWrex x A (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCtfin N)))
      y A N dv_cache_0052 dv_cache_0021 dv_cache_0053 p0132
  have p0134 :=
    @gSyl (.classMem N (synCnnc))
      (synWral y N (.imp (synWss (.cv y) (synCnnc))
          (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin N))))
      (.imp (.classMem A N) (.imp (synWss A (synCnnc))
          (.classMem (.cab a (synWrex x A (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCtfin N))))
      p0127 p0133
  have p0135 :=
    @gCom23 (.classMem N (synCnnc)) (.classMem A N) (synWss A (synCnnc))
      (.classMem (.cab a (synWrex x A (.classEq (.cv a) (synCtfin (.cv x))))) (synCtfin N))
      p0134
  have p0136 :=
    @gN3imp (.classMem N (synCnnc)) (synWss A (synCnnc)) (.classMem A N)
      (.classMem (.cab a (synWrex x A (.classEq (.cv a) (synCtfin (.cv x))))) (synCtfin N))
      p0135
  exact p0136


end NFChoice.DirectNominalPrf.WPPReplay
