/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block019

/-! NF weak partition development: NominalWPPReplayChunk017Compact001Part083. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hninjraisedselfcutalldndv`. -/
@[expose]
noncomputable def gHninjraisedselfcutalldndv (x : Var) (u : Var) (A : Class) (f : Var)
    (s : Var) (r : Var) (_dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (_dv_A_s : s ∉ A.fv)
    (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (_dv_f_r : f ≠ r) (_dv_f_s : f ≠ s)
    (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) (_dv_r_s : r ≠ s) (dv_r_u : r ≠ u) (dv_r_x : r ≠ x)
    (dv_s_u : s ≠ u) (dv_s_x : s ≠ x) (dv_u_x : u ≠ x)
    (hyp_hninjraisedselfcutalldndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
        (synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ ({ f } : Finset Var) ∪
        ({ s } : Finset Var) ∪
      ({ r } : Finset Var)
  let a : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let w : Var := freshVar proofSupport 4
  let v : Var := freshVar proofSupport 5
  let k : Var := freshVar proofSupport 6
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_ne_f : a ≠ f := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_a_ne_s : a ≠ s := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_s : y ≠ s := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_b_ne_f : b ≠ f := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_b_ne_s : b ≠ s := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_s : z ≠ s := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_ne_f : w ≠ f := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_s : w ≠ s := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_r : w ≠ r := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_ne_f : v ≠ f := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_s : v ≠ s := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_r : v ≠ r := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_v : r ≠ v := Ne.symm fresh_v_ne_r
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_k_ne_u : k ≠ u := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_k_ne_f : k ≠ f := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_k_ne_s : k ≠ s := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_r : k ≠ r := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_w : a ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_w_ne_a : w ≠ a := Ne.symm fresh_a_ne_w
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_b_ne_z : b ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_b_ne_w : b ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_w_ne_b : w ≠ b := Ne.symm fresh_b_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_v_ne_k : v ≠ k :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_k_ne_v : k ≠ v := Ne.symm fresh_v_ne_k
  have dv_cache_0001 : Disjoint ((synChwcn A)).fv ((Class.cv r)).fv := by
    exact
      (show Disjoint ((synChwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact dv_A_r))))))
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0003 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0004 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0005 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0006 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0007 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : b ∉ ((synCcnv (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_f,
          not_false_eq_true])
  have dv_cache_0010 :
    b ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (.cv f)) (.cv x) (.cv y))
            (synWbr (.cv a) (synCwe) (.cv y)))
          (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_f, fresh_b_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((synCrn (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_f_x), not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
            (synWbr (.cv a) (synCwe) (.cv y)))
          (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_f_x), fresh_x_ne_y, fresh_x_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((synChnord A)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_y_not_A, not_false_eq_true])
  have dv_cache_0014 :
    y ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
            (synWbr (.cv a) (synCwe) (synChnord A)))
          (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_f, fresh_y_not_A, fresh_y_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_s, not_false_eq_true])
  have dv_cache_0016 :
    a ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
            (synWbr (.cv s) (synCwe) (synChnord A)))
          (synWbr (synCpwpull (synCcnv (.cv f)) (.cv s)) (synCwe) (synCrn (.cv f))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_f, fresh_a_not_A, fresh_a_ne_s,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    b ∉
      ((Wff.imp (synWfo (synCcnv (.cv f)) (.cv x) (.cv y))
          (synWss (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCxp (.cv x) (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_f, fresh_b_ne_a,
          or_false, not_false_eq_true])
  have dv_cache_0018 :
    x ∉
      ((Wff.imp (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
          (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
            (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_f_x), fresh_x_ne_y, fresh_x_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    y ∉
      ((Wff.imp (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
          (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
            (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_f, fresh_y_not_A, fresh_y_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((Wff.imp (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
          (synWss (synCpwpull (synCcnv (.cv f)) (.cv s))
            (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_f, fresh_a_not_A, fresh_a_ne_s, or_false,
          not_false_eq_true])
  have dv_cache_0021 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0022 : z ∉ ((Class.cv y)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0023 : z ∉ ((synCcom (.cv f) (.cv s))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_f, fresh_z_ne_s, or_false, not_false_eq_true])
  have dv_cache_0024 : z ∉ ((synCcnv (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0025 :
    z ∉
      ((synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_f, fresh_z_ne_r, fresh_z_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0026 : z ∉ ((Wff.classMem (.cv x) (synCdm (synCcnv (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, or_false, not_false_eq_true])
  have dv_cache_0027 : z ∉ ((synCfv (synCcnv (.cv f)) (.cv x))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, or_false, not_false_eq_true])
  have dv_cache_0028 :
    z ∉
      ((synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, fresh_z_ne_y, fresh_z_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0029 : w ∉ ((synCfv (synCcnv (.cv f)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0030 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0031 : w ∉ ((Class.cv f)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_f, not_false_eq_true])
  have dv_cache_0032 : w ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_s, not_false_eq_true])
  have dv_cache_0033 :
    w ∉
      ((synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_f, fresh_w_ne_r, fresh_w_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0034 : w ∉ ((Wff.classMem (.cv y) (synCdm (synCcnv (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0035 : w ∉ ((synCfv (synCcnv (.cv f)) (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0036 :
    w ∉
      ((synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, fresh_w_ne_y, fresh_w_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0037 : w ∉ ((Class.cv x)).fv :=
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
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0038 :
    z ∉
      ((synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
            (.classMem (.cv y) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv y))))).fv :=
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
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, fresh_z_ne_y, fresh_z_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0039 :
    w ∉
      ((synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
            (.classMem (.cv y) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv y))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, fresh_w_ne_y, fresh_w_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0040 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0041 :
    x ∉ ((synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_f_x), (Ne.symm dv_s_x), or_false,
          not_false_eq_true])
  have dv_cache_0042 :
    y ∉ ((synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_f, fresh_y_ne_s, or_false, not_false_eq_true])
  have dv_cache_0043 :
    x ∉
      ((synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w)))))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_z, (Ne.symm dv_f_x),
          fresh_x_ne_w, (Ne.symm dv_s_x), or_false, and_false, not_false_eq_true])
  have dv_cache_0044 :
    y ∉
      ((synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w)))))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_f,
          fresh_y_ne_w, fresh_y_ne_s, or_false, and_false, not_false_eq_true])
  have dv_cache_0045 :
    x ∉
      ((synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, (Ne.symm dv_f_x), (Ne.symm dv_r_x),
          (Ne.symm dv_s_x), or_false, not_false_eq_true])
  have dv_cache_0046 :
    y ∉
      ((synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_f, fresh_y_ne_r, fresh_y_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0047 : b ∉ ((synCfv (synCcnv (.cv f)) (.cv w))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_w, fresh_b_ne_f, or_false, not_false_eq_true])
  have dv_cache_0048 : b ∉ ((synCdm (.cv f))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_f,
          not_false_eq_true])
  have dv_cache_0049 :
    b ∉
      ((synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
            (.classEq (.cv w) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w)))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv w))))).fv :=
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
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_f, fresh_b_ne_w, fresh_b_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0050 :
    b ∉ ((Wff.classEq (.cv a) (synCfv (synCcnv (.cv f)) (.cv z)))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_z, fresh_b_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0051 : a ∉ ((synCfv (synCcnv (.cv f)) (.cv z))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_f, or_false, not_false_eq_true])
  have dv_cache_0052 : a ∉ ((synCdm (.cv f))).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_f,
          not_false_eq_true])
  have dv_cache_0053 :
    a ∉
      ((synWrex b (synCdm (.cv f)) (synWa (synWa
              (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
              (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s) (.cv b))))).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_f, fresh_a_ne_z,
          fresh_a_ne_w, fresh_a_ne_b, fresh_a_ne_s, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0054 :
    a ∉
      ((synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_f, fresh_a_ne_w, fresh_a_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0055 :
    b ∉
      ((synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_f, fresh_b_ne_w, fresh_b_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0056 : a ∉ ((synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_f, or_false, not_false_eq_true])
  have dv_cache_0057 : b ∉ ((synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_f, or_false, not_false_eq_true])
  have dv_cache_0058 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0059 : z ∉ ((synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_f, or_false, not_false_eq_true])
  have dv_cache_0060 : w ∉ ((synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0061 : w ∉ ((synCdm (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_f,
          not_false_eq_true])
  have dv_cache_0062 : z ∉ ((synCdm (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0063 : a ∉ ((synCrn (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_f,
          not_false_eq_true])
  have dv_cache_0064 : b ∉ ((synCrn (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_f,
          not_false_eq_true])
  have dv_cache_0065 : a ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_f, not_false_eq_true])
  have dv_cache_0066 : b ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_f, not_false_eq_true])
  have dv_cache_0067 : z ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_f, not_false_eq_true])
  have dv_cache_0068 : b ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_s, not_false_eq_true])
  have dv_cache_0069 : z ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_s, not_false_eq_true])
  have dv_cache_0070 : w ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact (show w ≠ a from (by exact fresh_w_ne_a))
  have dv_cache_0071 : w ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact (show w ≠ b from (by exact fresh_w_ne_b))
  have dv_cache_0072 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0073 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0074 : b ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073
    exact (show b ≠ z from (by exact fresh_b_ne_z))
  have dv_cache_0075 :
    u ∉
      ((synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_f_u), (Ne.symm dv_s_u), or_false,
          not_false_eq_true])
  have dv_cache_0076 : u ∉ ((synChwcn (synCpw1 (synCpw1 A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_A_u,
          not_false_eq_true])
  have dv_cache_0077 :
    u ∉
      ((synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
          (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
          (synCrn (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, dv_A_u, (Ne.symm dv_f_u), (Ne.symm dv_r_u),
          (Ne.symm dv_s_u), or_false, not_false_eq_true])
  have dv_cache_0078 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0079 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0080 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0081 :
    v ∉
      ((synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, fresh_v_ne_f, fresh_v_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0082 :
    k ∉
      ((synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_f, fresh_k_not_A, fresh_k_ne_r, fresh_k_ne_v,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0083 :
    k ∉
      ((synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWa (.classMem (.cv v) (synChwcn A)) (synWa
              (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
                (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
              (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_u, fresh_k_not_A, fresh_k_ne_v, fresh_k_ne_f,
          fresh_k_ne_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0084 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
    exact (show r ≠ v from (by exact fresh_r_ne_v))
  have dv_cache_0085 : u ∉ ((synCpw1 (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_A_u,
          not_false_eq_true])
  have dv_cache_0086 :
    k ∉
      ((synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_k_not_A, fresh_k_ne_f, fresh_k_ne_r, fresh_k_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0087 : k ∉ ((synCpw1 (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_k_not_A,
          not_false_eq_true])
  have dv_cache_0088 :
    k ∉
      ((synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_v, fresh_k_not_A, or_false, not_false_eq_true])
  have dv_cache_0089 :
    k ∉
      ((synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_v, fresh_k_not_A, fresh_k_ne_f, fresh_k_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0090 : Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
    exact
      (show Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ u from (by exact Ne.symm dv_u_x)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0091 : x ∉ ((synCfv (.cv f) (synCec (.cv v) (synChwniso A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, dv_A_x, (Ne.symm dv_f_x), or_false,
          not_false_eq_true])
  have dv_cache_0092 : x ∉ ((synCfv (synC2nd) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0093 :
    x ∉
      ((synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), fresh_x_ne_v, dv_A_x, (Ne.symm dv_f_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0094 :
    v ∉
      ((synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_A, fresh_v_ne_f, fresh_v_ne_r, fresh_v_ne_s,
          or_false, not_false_eq_true])
  have dv_cache_0095 :
    v ∉
      ((synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_x,
          fresh_v_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0096 :
    u ∉
      ((synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
      dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
      dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, dv_A_u, (Ne.symm dv_f_u), (Ne.symm dv_r_u),
          (Ne.symm dv_s_u), or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A))))
  have p0001 := @gF1f1orn (synChnord A) (synCpw1 (synCpw1 A)) (.cv f)
  have p0002 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (synWf1o (.cv f) (synChnord A) (synCrn (.cv f))) p0000 p0001
  have p0003 := @gF1ocnv (synChnord A) (synCrn (.cv f)) (.cv f)
  have p0004 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (.cv f) (synChnord A) (synCrn (.cv f)))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A)) p0002 p0003
  have p0005 :=
    @gSimpr (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A))))
  have p0006 :=
    @gSimpl (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))
  have p0007 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A))))
      (.classEq (.cv r) (synChncodecmpset A)) p0005 p0006
  have p0008 :=
    @gJctil
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classEq (.cv r) (synChncodecmpset A)) (.classMem A (synCvv)) p0007
      hyp_hninjraisedselfcutalldndv_1
  have p0009 := @gSimpl (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A))
  have p0010 := @gHncodecmpsetexg A
  have p0011 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0009 p0010
  have p0012 := @gSimpr (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A))
  have p0013 :=
    @gEleq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synCvv) p0012
  have p0014 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem (.cv r) (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0011
      p0013
  have p0016 := @gHwcnexg A
  have p0017 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv)) p0009 p0016
  have p0018 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)) p0014 p0017
  have p0020 := @gHncodecmpsetrefndv A
  have p0021 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
      p0009 p0020
  have p0023 :=
    @gBreq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCref) p0012
  have p0024 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv r) (synCref) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCref) (synChwcn A)) p0021 p0023
  have p0026 := @gHncodecmpsettransndv A
  have p0027 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A))
      p0009 p0026
  have p0029 :=
    @gBreq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCtrans) p0012
  have p0030 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv r) (synCtrans) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)) p0027 p0029
  have p0031 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv r) (synCref) (synChwcn A))
      (synWbr (.cv r) (synCtrans) (synChwcn A)) p0024 p0030
  have p0033 := @gHncodecmpsetconnexndv A
  have p0034 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A))
      p0009 p0033
  have p0036 :=
    @gBreq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCconnex) p0012
  have p0037 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (.cv r) (synCconnex) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)) p0034 p0036
  have p0038 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (synWbr (.cv r) (synCref) (synChwcn A))
        (synWbr (.cv r) (synCtrans) (synChwcn A)))
      (synWbr (.cv r) (synCconnex) (synChwcn A)) p0031 p0037
  have p0039 := @gHncodecmpsetssxpndv A
  have p0040 :=
    @gA1i (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)))
      (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A))) p0039
  have p0042 :=
    @gSseq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)) p0012
  have p0043 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))
      (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A))) p0040 p0042
  have p0044 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
          (synWbr (.cv r) (synCtrans) (synChwcn A)))
        (synWbr (.cv r) (synCconnex) (synChwcn A)))
      (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))) p0038 p0043
  have p0045 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (synWa (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
            (synWbr (.cv r) (synCtrans) (synChwcn A)))
          (synWbr (.cv r) (synCconnex) (synChwcn A)))
        (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))))
      p0018 p0044
  have p0047 := @gHncodecmpstrictfrndv A
  have p0048 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv))
      (synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (synCfound) (synChwcn A))
      p0009 p0047
  have p0051 :=
    @gCnveqd (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) p0012
  have p0052 :=
    @gDifeq12d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synCcnv (.cv r)) (synCcnv (synChncodecmpset A))
      p0012 p0051
  have p0053 :=
    @gBreq1d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synCdif (.cv r) (synCcnv (.cv r)))
      (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (synChwcn A)
      (synCfound) p0052
  have p0054 :=
    @gMpbird (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (synChwcn A))
      (synWbr (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (synCfound) (synChwcn A))
      p0048 p0053
  have p0055 :=
    @gJca (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv))) (synWa
          (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
              (synWbr (.cv r) (synCtrans) (synChwcn A)))
            (synWbr (.cv r) (synCconnex) (synChwcn A)))
          (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))))
      (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (synChwcn A)) p0045
      p0054
  have p0056 := @gLnqordwe (synChwcn A) (.cv r) dv_cache_0001
  have p0057 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
          (synWa (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
                (synWbr (.cv r) (synCtrans) (synChwcn A)))
              (synWbr (.cv r) (synCconnex) (synChwcn A)))
            (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))))
        (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (synChwcn A)))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synClnquo (.cv r) (synChwcn A)))
      p0055 p0056
  have p0059 := @gLnkereq (.cv r) (synChncodecmpset A)
  have p0060 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (synClnker (.cv r)) (synClnker (synChncodecmpset A))) p0012 p0059
  have p0062 := @gHncodecmplnkerndv A
  have p0063 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem A (synCvv))
      (.classEq (synClnker (synChncodecmpset A)) (synChwniso A)) p0009 p0062
  have p0064 :=
    @gEqtrd (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synClnker (.cv r)) (synClnker (synChncodecmpset A)) (synChwniso A) p0060 p0063
  have p0065 := @gHnordlnquoeqimndv A r dv_cache_0002
  have p0066 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classEq (synClnker (.cv r)) (synChwniso A))
      (.classEq (synClnquo (.cv r) (synChwcn A)) (synChnord A)) p0064 p0065
  have p0067 :=
    @gBreq2d (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synClnquo (.cv r) (synChwcn A)) (synChnord A)
      (synClnqord (.cv r) (synChwcn A)) (synCwe) p0066
  have p0068 :=
    @gMpbid (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synClnquo (.cv r) (synChwcn A)))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synChnord A)) p0057 p0067
  have p0069 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem A (synCvv)) (.classEq (.cv r) (synChncodecmpset A)))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synChnord A)) p0008 p0068
  have p0071 :=
    @gSimpr (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))
  have p0072 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A))))
      (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A))) p0005 p0071
  have p0073 :=
    @gBreq1d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.cv s) (synClnqord (.cv r) (synChwcn A)) (synChnord A) (synCwe) p0072
  have p0074 :=
    @gMpbird
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (.cv s) (synCwe) (synChnord A))
      (synWbr (synClnqord (.cv r) (synChwcn A)) (synCwe) (synChnord A)) p0069 p0073
  have p0075 :=
    @gJca
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWbr (.cv s) (synCwe) (synChnord A)) p0004 p0074
  have p0076 := @gVex s
  have p0077 := @gBiid (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
  have p0078 :=
    @gA1i
      (synWb (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A)))
      (.classEq (.cv a) (.cv s)) p0077
  have p0079 := @gId (.classEq (.cv a) (.cv s))
  have p0080 :=
    @gBreq1d (.classEq (.cv a) (.cv s)) (.cv a) (.cv s) (synChnord A) (synCwe) p0079
  have p0081 :=
    @gAnbi12d (.classEq (.cv a) (.cv s))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWbr (.cv a) (synCwe) (synChnord A))
      (synWbr (.cv s) (synCwe) (synChnord A)) p0078 p0080
  have p0083 :=
    @gCoeq2d (.classEq (.cv a) (.cv s)) (.cv a) (.cv s) (synCcnv (synCcnv (.cv f)))
      p0079
  have p0084 :=
    @gCoeq1d (.classEq (.cv a) (.cv s)) (synCcom (synCcnv (synCcnv (.cv f))) (.cv a))
      (synCcom (synCcnv (synCcnv (.cv f))) (.cv s)) (synCcnv (.cv f)) p0083
  have p0085 := (Nominal.classEqRefl (synCpwpull (synCcnv (.cv f)) (.cv a)))
  have p0086 :=
    @gEqcomi (synCpwpull (synCcnv (.cv f)) (.cv a))
      (synCcom (synCcom (synCcnv (synCcnv (.cv f))) (.cv a)) (synCcnv (.cv f))) p0085
  have p0087 := (Nominal.classEqRefl (synCpwpull (synCcnv (.cv f)) (.cv s)))
  have p0088 :=
    @gEqcomi (synCpwpull (synCcnv (.cv f)) (.cv s))
      (synCcom (synCcom (synCcnv (synCcnv (.cv f))) (.cv s)) (synCcnv (.cv f))) p0087
  have p0089 :=
    @gN3eqtr3g (.classEq (.cv a) (.cv s))
      (synCcom (synCcom (synCcnv (synCcnv (.cv f))) (.cv a)) (synCcnv (.cv f)))
      (synCcom (synCcom (synCcnv (synCcnv (.cv f))) (.cv s)) (synCcnv (.cv f)))
      (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCpwpull (synCcnv (.cv f)) (.cv s))
      p0084 p0086 p0088
  have p0090 :=
    @gBreq1d (.classEq (.cv a) (.cv s)) (synCpwpull (synCcnv (.cv f)) (.cv a))
      (synCpwpull (synCcnv (.cv f)) (.cv s)) (synCrn (.cv f)) (synCwe) p0089
  have p0091 :=
    @gImbi12d (.classEq (.cv a) (.cv s))
      (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWbr (.cv a) (synCwe) (synChnord A)))
      (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWbr (.cv s) (synCwe) (synChnord A)))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f)))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv s)) (synCwe) (synCrn (.cv f))) p0081
      p0090
  have p0092 := @gHnordex A hyp_hninjraisedselfcutalldndv_1
  have p0093 := @gF1oeq3 (.cv y) (synChnord A) (synCrn (.cv f)) (synCcnv (.cv f))
  have p0094 := @gId (.classEq (.cv y) (synChnord A))
  have p0095 :=
    @gBreq2d (.classEq (.cv y) (synChnord A)) (.cv y) (synChnord A) (.cv a) (synCwe)
      p0094
  have p0096 :=
    @gAnbi12d (.classEq (.cv y) (synChnord A))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWbr (.cv a) (synCwe) (.cv y)) (synWbr (.cv a) (synCwe) (synChnord A)) p0093
      p0095
  have p0097 :=
    @gBiid (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f)))
  have p0098 :=
    @gA1i
      (synWb (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f)))
        (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))))
      (.classEq (.cv y) (synChnord A)) p0097
  have p0099 :=
    @gImbi12d (.classEq (.cv y) (synChnord A))
      (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
        (synWbr (.cv a) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWbr (.cv a) (synCwe) (synChnord A)))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f)))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))) p0096
      p0098
  have p0100 := @gVex f
  have p0101 := @gRnexg (.cv f) (synCvv)
  have p0102 := Nominal.mp p0100 p0101
  have p0103 := @gF1oeq2 (.cv x) (synCrn (.cv f)) (.cv y) (synCcnv (.cv f))
  have p0104 := @gBiid (synWbr (.cv a) (synCwe) (.cv y))
  have p0105 :=
    @gA1i
      (synWb (synWbr (.cv a) (synCwe) (.cv y)) (synWbr (.cv a) (synCwe) (.cv y)))
      (.classEq (.cv x) (synCrn (.cv f))) p0104
  have p0106 :=
    @gAnbi12d (.classEq (.cv x) (synCrn (.cv f)))
      (synWf1o (synCcnv (.cv f)) (.cv x) (.cv y))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
      (synWbr (.cv a) (synCwe) (.cv y)) (synWbr (.cv a) (synCwe) (.cv y)) p0103 p0105
  have p0107 := @gId (.classEq (.cv x) (synCrn (.cv f)))
  have p0108 :=
    @gBreq2d (.classEq (.cv x) (synCrn (.cv f))) (.cv x) (synCrn (.cv f))
      (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) p0107
  have p0109 :=
    @gImbi12d (.classEq (.cv x) (synCrn (.cv f)))
      (synWa (synWf1o (synCcnv (.cv f)) (.cv x) (.cv y)) (synWbr (.cv a) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
        (synWbr (.cv a) (synCwe) (.cv y)))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (.cv x))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))) p0106
      p0108
  have p0111 := @gCnvexg (.cv f) (synCvv)
  have p0112 := Nominal.mp p0100 p0111
  have p0113 := @gF1oeq1 (.cv x) (.cv y) (.cv b) (synCcnv (.cv f))
  have p0115 :=
    @gA1i
      (synWb (synWbr (.cv a) (synCwe) (.cv y)) (synWbr (.cv a) (synCwe) (.cv y)))
      (.classEq (.cv b) (synCcnv (.cv f))) p0104
  have p0116 :=
    @gAnbi12d (.classEq (.cv b) (synCcnv (.cv f))) (synWf1o (.cv b) (.cv x) (.cv y))
      (synWf1o (synCcnv (.cv f)) (.cv x) (.cv y)) (synWbr (.cv a) (synCwe) (.cv y))
      (synWbr (.cv a) (synCwe) (.cv y)) p0113 p0115
  have p0117 := @gId (.classEq (.cv b) (synCcnv (.cv f)))
  have p0118 :=
    @gCnveqd (.classEq (.cv b) (synCcnv (.cv f))) (.cv b) (synCcnv (.cv f)) p0117
  have p0119 :=
    @gCoeq1d (.classEq (.cv b) (synCcnv (.cv f))) (synCcnv (.cv b))
      (synCcnv (synCcnv (.cv f))) (.cv a) p0118
  have p0121 :=
    @gCoeq12d (.classEq (.cv b) (synCcnv (.cv f))) (synCcom (synCcnv (.cv b)) (.cv a))
      (synCcom (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv b) (synCcnv (.cv f)) p0119
      p0117
  have p0122 := (Nominal.classEqRefl (synCpwpull (.cv b) (.cv a)))
  have p0123 :=
    @gEqcomi (synCpwpull (.cv b) (.cv a))
      (synCcom (synCcom (synCcnv (.cv b)) (.cv a)) (.cv b)) p0122
  have p0126 :=
    @gN3eqtr3g (.classEq (.cv b) (synCcnv (.cv f)))
      (synCcom (synCcom (synCcnv (.cv b)) (.cv a)) (.cv b))
      (synCcom (synCcom (synCcnv (synCcnv (.cv f))) (.cv a)) (synCcnv (.cv f)))
      (synCpwpull (.cv b) (.cv a)) (synCpwpull (synCcnv (.cv f)) (.cv a)) p0121 p0123
      p0086
  have p0127 :=
    @gBreq1d (.classEq (.cv b) (synCcnv (.cv f))) (synCpwpull (.cv b) (.cv a))
      (synCpwpull (synCcnv (.cv f)) (.cv a)) (.cv x) (synCwe) p0126
  have p0128 :=
    @gImbi12d (.classEq (.cv b) (synCcnv (.cv f)))
      (synWa (synWf1o (.cv b) (.cv x) (.cv y)) (synWbr (.cv a) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (.cv f)) (.cv x) (.cv y)) (synWbr (.cv a) (synCwe) (.cv y)))
      (synWbr (synCpwpull (.cv b) (.cv a)) (synCwe) (.cv x))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (.cv x)) p0116 p0127
  have p0129 :=
    @gPwpullwesetimpndv x y b a dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0130 :=
    @gVtocl
      (.imp (synWa (synWf1o (.cv b) (.cv x) (.cv y)) (synWbr (.cv a) (synCwe) (.cv y)))
        (synWbr (synCpwpull (.cv b) (.cv a)) (synCwe) (.cv x)))
      (.imp (synWa (synWf1o (synCcnv (.cv f)) (.cv x) (.cv y))
          (synWbr (.cv a) (synCwe) (.cv y)))
        (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (.cv x)))
      b (synCcnv (.cv f)) dv_cache_0009 dv_cache_0010 p0112 p0128 p0129
  have p0131 :=
    @gVtocl
      (.imp (synWa (synWf1o (synCcnv (.cv f)) (.cv x) (.cv y))
          (synWbr (.cv a) (synCwe) (.cv y)))
        (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (.cv x)))
      (.imp (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
          (synWbr (.cv a) (synCwe) (.cv y)))
        (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))))
      x (synCrn (.cv f)) dv_cache_0011 dv_cache_0012 p0102 p0109 p0130
  have p0132 :=
    @gVtocl
      (.imp (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
          (synWbr (.cv a) (synCwe) (.cv y)))
        (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))))
      (.imp (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
          (synWbr (.cv a) (synCwe) (synChnord A)))
        (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))))
      y (synChnord A) dv_cache_0013 dv_cache_0014 p0092 p0099 p0131
  have p0133 :=
    @gVtocl
      (.imp (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
          (synWbr (.cv a) (synCwe) (synChnord A)))
        (synWbr (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCwe) (synCrn (.cv f))))
      (.imp (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
          (synWbr (.cv s) (synCwe) (synChnord A)))
        (synWbr (synCpwpull (synCcnv (.cv f)) (.cv s)) (synCwe) (synCrn (.cv f))))
      a (.cv s) dv_cache_0015 dv_cache_0016 p0076 p0091 p0132
  have p0134 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWbr (.cv s) (synCwe) (synChnord A)))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv s)) (synCwe) (synCrn (.cv f))) p0075
      p0133
  have p0136 := @gCnvcnv (.cv f)
  have p0137 := @gCoeq1i (synCcnv (synCcnv (.cv f))) (.cv f) (.cv s) p0136
  have p0138 :=
    @gCoeq1i (synCcom (synCcnv (synCcnv (.cv f))) (.cv s)) (synCcom (.cv f) (.cv s))
      (synCcnv (.cv f)) p0137
  have p0139 :=
    @gEqtri (synCpwpull (synCcnv (.cv f)) (.cv s))
      (synCcom (synCcom (synCcnv (synCcnv (.cv f))) (.cv s)) (synCcnv (.cv f)))
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) p0087 p0138
  have p0140 :=
    @gBreq1i (synCpwpull (synCcnv (.cv f)) (.cv s))
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f)) (synCwe)
      p0139
  have p0141 :=
    @gSylib
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (synCpwpull (synCcnv (.cv f)) (.cv s)) (synCwe) (synCrn (.cv f)))
      (synWbr (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCwe)
        (synCrn (.cv f)))
      p0134 p0140
  have p0142 := @gF1f (synChnord A) (synCpw1 (synCpw1 A)) (.cv f)
  have p0143 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (synWf (.cv f) (synChnord A) (synCpw1 (synCpw1 A))) p0000 p0142
  have p0144 := @gFrn (synChnord A) (synCpw1 (synCpw1 A)) (.cv f)
  have p0145 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (synWss (synCrn (.cv f)) (synCpw1 (synCpw1 A))) p0143 p0144
  have p0146 :=
    @gJca
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCwe)
        (synCrn (.cv f)))
      (synWss (synCrn (.cv f)) (synCpw1 (synCpw1 A))) p0141 p0145
  have p0149 :=
    @gPm32i (.classMem (.cv f) (synCvv)) (.classMem (.cv s) (synCvv)) p0100 p0076
  have p0150 := @gCoexg (.cv f) (.cv s) (synCvv) (synCvv)
  have p0151 := Nominal.mp p0149 p0150
  have p0155 :=
    @gPm32i (.classMem (synCcom (.cv f) (.cv s)) (synCvv))
      (.classMem (synCcnv (.cv f)) (synCvv)) p0151 p0112
  have p0156 := @gCoexg (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)) (synCvv) (synCvv)
  have p0157 := Nominal.mp p0155 p0156
  have p0161 :=
    @gElhwcodesclndv (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
      (synCrn (.cv f)) (synCpw1 (synCpw1 A)) p0157 p0102
  have p0162 :=
    @gSylibr
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (synWbr (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCwe)
          (synCrn (.cv f))) (synWss (synCrn (.cv f)) (synCpw1 (synCpw1 A))))
      (.classMem (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChwcodes (synCpw1 (synCpw1 A))))
      p0146 p0161
  have p0163 := @gF1ofo (synCrn (.cv f)) (synChnord A) (synCcnv (.cv f))
  have p0164 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A)) p0004 p0163
  have p0166 := @gBiid (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
  have p0167 :=
    @gA1i
      (synWb (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A)))
      (.classEq (.cv a) (.cv s)) p0166
  have p0176 :=
    @gSseq1d (.classEq (.cv a) (.cv s)) (synCpwpull (synCcnv (.cv f)) (.cv a))
      (synCpwpull (synCcnv (.cv f)) (.cv s))
      (synCxp (synCrn (.cv f)) (synCrn (.cv f))) p0089
  have p0177 :=
    @gImbi12d (.classEq (.cv a) (.cv s))
      (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv s))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      p0167 p0176
  have p0179 := @gFoeq3 (.cv y) (synChnord A) (synCrn (.cv f)) (synCcnv (.cv f))
  have p0180 :=
    @gBiid
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
  have p0181 :=
    @gA1i
      (synWb (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
          (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
        (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
          (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))
      (.classEq (.cv y) (synChnord A)) p0180
  have p0182 :=
    @gImbi12d (.classEq (.cv y) (synChnord A))
      (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
      (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      p0179 p0181
  have p0186 := @gFoeq2 (.cv x) (synCrn (.cv f)) (.cv y) (synCcnv (.cv f))
  have p0189 :=
    @gXpeq12d (.classEq (.cv x) (synCrn (.cv f))) (.cv x) (synCrn (.cv f)) (.cv x)
      (synCrn (.cv f)) p0107 p0107
  have p0190 :=
    @gSseq2d (.classEq (.cv x) (synCrn (.cv f))) (synCxp (.cv x) (.cv x))
      (synCxp (synCrn (.cv f)) (synCrn (.cv f)))
      (synCpwpull (synCcnv (.cv f)) (.cv a)) p0189
  have p0191 :=
    @gImbi12d (.classEq (.cv x) (synCrn (.cv f)))
      (synWfo (synCcnv (.cv f)) (.cv x) (.cv y))
      (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCxp (.cv x) (.cv x)))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      p0186 p0190
  have p0195 := @gFoeq1 (.cv x) (.cv y) (.cv b) (synCcnv (.cv f))
  have p0206 :=
    @gSseq1d (.classEq (.cv b) (synCcnv (.cv f))) (synCpwpull (.cv b) (.cv a))
      (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCxp (.cv x) (.cv x)) p0126
  have p0207 :=
    @gImbi12d (.classEq (.cv b) (synCcnv (.cv f))) (synWfo (.cv b) (.cv x) (.cv y))
      (synWfo (synCcnv (.cv f)) (.cv x) (.cv y))
      (synWss (synCpwpull (.cv b) (.cv a)) (synCxp (.cv x) (.cv x)))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCxp (.cv x) (.cv x))) p0195
      p0206
  have p0208 :=
    @gPwpullssxpsetimpndv x y b a dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0209 :=
    @gVtocl
      (.imp (synWfo (.cv b) (.cv x) (.cv y))
        (synWss (synCpwpull (.cv b) (.cv a)) (synCxp (.cv x) (.cv x))))
      (.imp (synWfo (synCcnv (.cv f)) (.cv x) (.cv y))
        (synWss (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCxp (.cv x) (.cv x))))
      b (synCcnv (.cv f)) dv_cache_0009 dv_cache_0017 p0112 p0207 p0208
  have p0210 :=
    @gVtocl
      (.imp (synWfo (synCcnv (.cv f)) (.cv x) (.cv y))
        (synWss (synCpwpull (synCcnv (.cv f)) (.cv a)) (synCxp (.cv x) (.cv x))))
      (.imp (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
        (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
          (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))
      x (synCrn (.cv f)) dv_cache_0011 dv_cache_0018 p0102 p0191 p0209
  have p0211 :=
    @gVtocl
      (.imp (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (.cv y))
        (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
          (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))
      (.imp (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
          (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))
      y (synChnord A) dv_cache_0013 dv_cache_0019 p0092 p0182 p0210
  have p0212 :=
    @gVtocl
      (.imp (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWss (synCpwpull (synCcnv (.cv f)) (.cv a))
          (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))
      (.imp (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
        (synWss (synCpwpull (synCcnv (.cv f)) (.cv s))
          (synCxp (synCrn (.cv f)) (synCrn (.cv f)))))
      a (.cv s) dv_cache_0015 dv_cache_0020 p0076 p0177 p0211
  have p0213 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWfo (synCcnv (.cv f)) (synCrn (.cv f)) (synChnord A))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv s))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      p0164 p0212
  have p0219 :=
    @gSseq1i (synCpwpull (synCcnv (.cv f)) (.cv s))
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
      (synCxp (synCrn (.cv f)) (synCrn (.cv f))) p0139
  have p0220 :=
    @gSylib
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWss (synCpwpull (synCcnv (.cv f)) (.cv s))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      (synWss (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      p0213 p0219
  have p0235 :=
    @gOpfv1st (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))
      p0157 p0102
  have p0236 :=
    @gEqcomi
      (synCfv (synC1st) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))))
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) p0235
  have p0251 :=
    @gOpfv2nd (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))
      p0157 p0102
  have p0267 :=
    @gXpeq12i
      (synCfv (synC2nd) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))))
      (synCrn (.cv f))
      (synCfv (synC2nd) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))))
      (synCrn (.cv f)) p0251 p0251
  have p0268 :=
    @gEqcomi
      (synCxp (synCfv (synC2nd)
          (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))))
        (synCfv (synC2nd) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
            (synCrn (.cv f)))))
      (synCxp (synCrn (.cv f)) (synCrn (.cv f))) p0267
  have p0269 :=
    @gSseq12i (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
      (synCfv (synC1st) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))))
      (synCxp (synCrn (.cv f)) (synCrn (.cv f)))
      (synCxp (synCfv (synC2nd)
          (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))))
        (synCfv (synC2nd) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
            (synCrn (.cv f)))))
      p0236 p0268
  have p0270 :=
    @gSylib
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWss (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synCxp (synCrn (.cv f)) (synCrn (.cv f))))
      (synWss (synCfv (synC1st)
          (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))))
        (synCxp (synCfv (synC2nd)
            (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
              (synCrn (.cv f)))) (synCfv (synC2nd)
            (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
              (synCrn (.cv f))))))
      p0220 p0269
  have p0271 :=
    @gJca
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChwcodes (synCpw1 (synCpw1 A))))
      (synWss (synCfv (synC1st)
          (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))))
        (synCxp (synCfv (synC2nd)
            (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
              (synCrn (.cv f)))) (synCfv (synC2nd)
            (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
              (synCrn (.cv f))))))
      p0162 p0270
  have p0286 :=
    @gPm32i
      (.classMem (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCvv))
      (.classMem (synCrn (.cv f)) (synCvv)) p0157 p0102
  have p0287 :=
    @gOpexg (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))
      (synCvv) (synCvv)
  have p0288 := Nominal.mp p0286 p0287
  have p0289 :=
    @gElhwcncl (synCpw1 (synCpw1 A))
      (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f)))
  have p0290 := Nominal.mp p0288 p0289
  have p0291 :=
    @gSylibr
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChwcodes (synCpw1 (synCpw1 A)))) (synWss
          (synCfv (synC1st) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
              (synCrn (.cv f)))) (synCxp (synCfv (synC2nd)
              (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
                (synCrn (.cv f)))) (synCfv (synC2nd)
              (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
                (synCrn (.cv f)))))))
      (.classMem (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChwcn (synCpw1 (synCpw1 A))))
      p0271 p0290
  have p0292 := @gF1odm (synChnord A) (synCrn (.cv f)) (.cv f)
  have p0293 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (.cv f) (synChnord A) (synCrn (.cv f)))
      (.classEq (synCdm (.cv f)) (synChnord A)) p0002 p0292
  have p0294 := @gF1oeq2 (synCdm (.cv f)) (synChnord A) (synCrn (.cv f)) (.cv f)
  have p0295 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classEq (synCdm (.cv f)) (synChnord A))
      (synWb (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWf1o (.cv f) (synChnord A) (synCrn (.cv f))))
      p0293 p0294
  have p0296 :=
    @gMpbird
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf1o (.cv f) (synChnord A) (synCrn (.cv f))) p0002 p0295
  have p0297 :=
    @gBrco z (.cv x) (.cv y) (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)) dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0298 := @gF1ocnv (synCdm (.cv f)) (synCrn (.cv f)) (.cv f)
  have p0299 := @gF1ofun (synCrn (.cv f)) (synCdm (.cv f)) (synCcnv (.cv f))
  have p0300 :=
    @gSyl (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synCdm (.cv f)))
      (synWfun (synCcnv (.cv f))) p0298 p0299
  have p0301 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) (synWfun (synCcnv (.cv f)))
      p0296 p0300
  have p0302 := @gFunbrfv2b (.cv x) (.cv z) (synCcnv (.cv f))
  have p0303 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWfun (synCcnv (.cv f)))
      (synWb (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
        (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))))
      p0301 p0302
  have p0304 :=
    @gAnbi1d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
      (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)) p0303
  have p0305 :=
    @gExbidv
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))
      (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))
      z dv_cache_0025 p0304
  have p0306 :=
    @gAnass (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
      (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))
  have p0307 :=
    @gExbii
      (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      z p0306
  have p0308 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWex z (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWex z (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))))
      p0305 p0307
  have p0309 :=
    @gN1942v (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))
      z dv_cache_0026
  have p0310 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWex z (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))))
      p0308 p0309
  have p0311 := @gEqcom (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)
  have p0312 :=
    @gAnbi1i (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
      (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
      (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)) p0311
  have p0313 :=
    @gExbii
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))
      (synWa (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))
      z p0312
  have p0314 := @gFvex (.cv x) (synCcnv (.cv f))
  have p0315 :=
    @gBreq1 (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)) (.cv y)
      (synCcom (.cv f) (.cv s))
  have p0316 :=
    @gCeqsexv (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y)) z
      (synCfv (synCcnv (.cv f)) (.cv x)) dv_cache_0027 dv_cache_0028 p0314 p0315
  have p0317 :=
    @gBitri
      (synWex z (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWex z (synWa (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y))
      p0313 p0316
  have p0318 :=
    @gAnbi2i
      (synWex z (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y))
      (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) p0317
  have p0319 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y)))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y)))
      p0310 p0318
  have p0320 := @gDfrn4 (.cv f)
  have p0321 := @gEleq2i (synCrn (.cv f)) (synCdm (synCcnv (.cv f))) (.cv x) p0320
  have p0322 :=
    @gBicomi (.classMem (.cv x) (synCrn (.cv f)))
      (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) p0321
  have p0323 :=
    @gAnbi1i (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (.classMem (.cv x) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y))
      p0322
  have p0324 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y)))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y)))
      p0319 p0323
  have p0325 :=
    @gSyl5bb
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv y))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv s)) (.cv y))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y)))
      p0297 p0324
  have p0326 :=
    @gBrco w (synCfv (synCcnv (.cv f)) (.cv x)) (.cv y) (.cv f) (.cv s) dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
  have p0327 := @gBrcnv (.cv y) (.cv w) (.cv f)
  have p0328 :=
    @gBicomi (synWbr (.cv y) (synCcnv (.cv f)) (.cv w))
      (synWbr (.cv w) (.cv f) (.cv y)) p0327
  have p0329 := @gFunbrfv2b (.cv y) (.cv w) (synCcnv (.cv f))
  have p0330 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWfun (synCcnv (.cv f)))
      (synWb (synWbr (.cv y) (synCcnv (.cv f)) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      p0301 p0329
  have p0331 :=
    @gSyl5bb (synWbr (.cv w) (.cv f) (.cv y))
      (synWbr (.cv y) (synCcnv (.cv f)) (.cv w))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
      p0328 p0330
  have p0332 :=
    @gAnbi2d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (.cv w) (.cv f) (.cv y))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)) p0331
  have p0333 :=
    @gExbidv
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
        (synWbr (.cv w) (.cv f) (.cv y)))
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      w dv_cache_0033 p0332
  have p0334 :=
    @gAncom (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
  have p0335 :=
    @gAnass (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
  have p0336 :=
    @gBitri
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      (synWa (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      p0334 p0335
  have p0337 :=
    @gExbii
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      w p0336
  have p0338 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))))
      (synWex w (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)))))
      p0333 p0337
  have p0339 :=
    @gN1942v (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)))
      w dv_cache_0034
  have p0340 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWex w (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)))))
      p0338 p0339
  have p0341 := @gEqcom (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)
  have p0342 :=
    @gAnbi1i (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
      (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)) p0341
  have p0343 :=
    @gExbii
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)))
      (synWa (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)))
      w p0342
  have p0344 := @gFvex (.cv y) (synCcnv (.cv f))
  have p0345 :=
    @gBreq2 (.cv w) (synCfv (synCcnv (.cv f)) (.cv y))
      (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
  have p0346 :=
    @gCeqsexv (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      w (synCfv (synCcnv (.cv f)) (.cv y)) dv_cache_0035 dv_cache_0036 p0344 p0345
  have p0347 :=
    @gBitri
      (synWex w (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      (synWex w (synWa (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0343 p0346
  have p0348 :=
    @gAnbi2i
      (synWex w (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) p0347
  have p0349 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w)))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0340 p0348
  have p0351 := @gEleq2i (synCrn (.cv f)) (synCdm (synCcnv (.cv f))) (.cv y) p0320
  have p0352 :=
    @gBicomi (.classMem (.cv y) (synCrn (.cv f)))
      (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) p0351
  have p0353 :=
    @gAnbi1i (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (.classMem (.cv y) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0352
  have p0354 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0349 p0353
  have p0355 :=
    @gSyl5bb
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0326 p0354
  have p0356 :=
    @gAnbi2d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (.classMem (.cv x) (synCrn (.cv f))) p0355
  have p0357 :=
    @gBitrd
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv y))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv s)) (.cv y)))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      p0325 p0356
  have p0358 :=
    @gAnass (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv y)))
  have p0359 :=
    @gBicomi
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      p0358
  have p0360 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv y))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0357 p0359
  have p0361 := @gVex x
  have p0362 := @gVex y
  have p0363 := @gSimpl (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0364 :=
    @gEleq1d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z)
      (.cv x) (synCrn (.cv f)) p0363
  have p0365 := @gSimpr (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0366 :=
    @gEleq1d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w)
      (.cv y) (synCrn (.cv f)) p0365
  have p0367 :=
    @gAnbi12d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv x) (synCrn (.cv f)))
      (.classMem (.cv w) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f))) p0364
      p0366
  have p0369 :=
    @gFveq2d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z)
      (.cv x) (synCcnv (.cv f)) p0363
  have p0371 :=
    @gFveq2d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w)
      (.cv y) (synCcnv (.cv f)) p0365
  have p0372 :=
    @gBreq12d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (synCfv (synCcnv (.cv f)) (.cv z)) (synCfv (synCcnv (.cv f)) (.cv x))
      (synCfv (synCcnv (.cv f)) (.cv w)) (synCfv (synCcnv (.cv f)) (.cv y)) (.cv s)
      p0369 p0371
  have p0373 :=
    @gAnbi12d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
      (synWa (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0367 p0372
  have p0374 :=
    @gEqid
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
  have p0375 :=
    @gBraba
      (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
          (.classMem (.cv w) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      z w (.cv x) (.cv y)
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
      dv_cache_0021 dv_cache_0037 dv_cache_0022 dv_cache_0030 dv_cache_0038 dv_cache_0039
      dv_cache_0040 p0361 p0362 p0373 p0374
  have p0376 :=
    @gBicomi
      (synWbr (.cv x) (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0375
  have p0377 :=
    @gSyl6bb
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv y))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWbr (.cv x) (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y))
      p0360 p0376
  have p0378 :=
    (Nominal.biimpRefl
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv y)))
  have p0379 :=
    (Nominal.biimpRefl (synWbr (.cv x) (synCopab z w (synWa
            (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y)))
  have p0380 :=
    @gN3bitr3g
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv y))
      (synWbr (.cv x) (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y))
      (.classMem (synCop (.cv x) (.cv y))
        (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))))
      (.classMem (synCop (.cv x) (.cv y)) (synCopab z w (synWa
            (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w))))))
      p0377 p0378 p0379
  have p0381 :=
    @gEqrelrdv
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      x y (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
      dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
      dv_cache_0008 p0380
  have p0382 :=
    @gA1d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classEq (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCopab z w (synWa
            (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w))))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) p0381
  have p0383 := @gF1ocnvdm (synCdm (.cv f)) (synCrn (.cv f)) (.cv z) (.cv f)
  have p0384 :=
    @gAdantrr (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv z) (synCrn (.cv f)))
      (.classMem (synCfv (synCcnv (.cv f)) (.cv z)) (synCdm (.cv f)))
      (.classMem (.cv w) (synCrn (.cv f))) p0383
  have p0385 :=
    @gN3adant3 (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
      (.classMem (synCfv (synCcnv (.cv f)) (.cv z)) (synCdm (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      p0384
  have p0386 := @gF1ocnvdm (synCdm (.cv f)) (synCrn (.cv f)) (.cv w) (.cv f)
  have p0387 :=
    @gAdantrl (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv w) (synCrn (.cv f)))
      (.classMem (synCfv (synCcnv (.cv f)) (.cv w)) (synCdm (.cv f)))
      (.classMem (.cv z) (synCrn (.cv f))) p0386
  have p0388 :=
    @gN3adant3 (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
      (.classMem (synCfv (synCcnv (.cv f)) (.cv w)) (synCdm (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      p0387
  have p0389 := @gF1ocnvfv2 (synCdm (.cv f)) (synCrn (.cv f)) (.cv z) (.cv f)
  have p0390 :=
    @gEqcomd
      (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (.classMem (.cv z) (synCrn (.cv f))))
      (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))) (.cv z) p0389
  have p0391 := @gF1ocnvfv2 (synCdm (.cv f)) (synCrn (.cv f)) (.cv w) (.cv f)
  have p0392 :=
    @gEqcomd
      (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (.classMem (.cv w) (synCrn (.cv f))))
      (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w))) (.cv w) p0391
  have p0393 :=
    @gAnim12dan (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv z) (synCrn (.cv f)))
      (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
      (.classMem (.cv w) (synCrn (.cv f)))
      (.classEq (.cv w) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w)))) p0390
      p0392
  have p0394 :=
    @gN3adant3 (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
      (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w)))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      p0393
  have p0395 :=
    @gSimp3 (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
  have p0396 := @gFveq2 (.cv b) (synCfv (synCcnv (.cv f)) (.cv w)) (.cv f)
  have p0397 :=
    @gEqeq2d (.classEq (.cv b) (synCfv (synCcnv (.cv f)) (.cv w)))
      (synCfv (.cv f) (.cv b)) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w)))
      (.cv w) p0396
  have p0398 :=
    @gAnbi2d (.classEq (.cv b) (synCfv (synCcnv (.cv f)) (.cv w)))
      (.classEq (.cv w) (synCfv (.cv f) (.cv b)))
      (.classEq (.cv w) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w))))
      (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z)))) p0397
  have p0399 :=
    @gBreq2 (.cv b) (synCfv (synCcnv (.cv f)) (.cv w))
      (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
  have p0400 :=
    @gAnbi12d (.classEq (.cv b) (synCfv (synCcnv (.cv f)) (.cv w)))
      (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
      (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w)))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s) (.cv b))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      p0398 p0399
  have p0401 :=
    @gRspcev
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
          (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s) (.cv b)))
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
          (.classEq (.cv w) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w)))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      b (synCfv (synCcnv (.cv f)) (.cv w)) (synCdm (.cv f)) dv_cache_0047 dv_cache_0048
      dv_cache_0049 p0400
  have p0402 :=
    @gSyl12anc
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      (.classMem (synCfv (synCcnv (.cv f)) (.cv w)) (synCdm (.cv f)))
      (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv w)))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      (synWrex b (synCdm (.cv f)) (synWa (synWa
            (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s) (.cv b))))
      p0388 p0394 p0395 p0401
  have p0403 := @gFveq2 (.cv a) (synCfv (synCcnv (.cv f)) (.cv z)) (.cv f)
  have p0404 :=
    @gEqeq2d (.classEq (.cv a) (synCfv (synCcnv (.cv f)) (.cv z)))
      (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z)))
      (.cv z) p0403
  have p0405 :=
    @gAnbi1d (.classEq (.cv a) (synCfv (synCcnv (.cv f)) (.cv z)))
      (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
      (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
      (.classEq (.cv w) (synCfv (.cv f) (.cv b))) p0404
  have p0406 := @gBreq1 (.cv a) (synCfv (synCcnv (.cv f)) (.cv z)) (.cv b) (.cv s)
  have p0407 :=
    @gAnbi12d (.classEq (.cv a) (synCfv (synCcnv (.cv f)) (.cv z)))
      (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
        (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
      (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
      (synWbr (.cv a) (.cv s) (.cv b))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s) (.cv b)) p0405 p0406
  have p0408 :=
    @gRexbidv (.classEq (.cv a) (synCfv (synCcnv (.cv f)) (.cv z)))
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
          (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
          (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s) (.cv b)))
      b (synCdm (.cv f)) dv_cache_0050 p0407
  have p0409 :=
    @gRspcev
      (synWrex b (synCdm (.cv f)) (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (synWrex b (synCdm (.cv f)) (synWa (synWa
            (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s) (.cv b))))
      a (synCfv (synCcnv (.cv f)) (.cv z)) (synCdm (.cv f)) dv_cache_0051 dv_cache_0052
      dv_cache_0053 p0408
  have p0410 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      (.classMem (synCfv (synCcnv (.cv f)) (.cv z)) (synCdm (.cv f)))
      (synWrex b (synCdm (.cv f)) (synWa (synWa
            (.classEq (.cv z) (synCfv (.cv f) (synCfv (synCcnv (.cv f)) (.cv z))))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s) (.cv b))))
      (synWrex a (synCdm (.cv f)) (synWrex b (synCdm (.cv f)) (synWa
            (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
              (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))))
      p0385 p0402 p0409
  have p0411 :=
    @gN3expib (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      (synWrex a (synCdm (.cv f)) (synWrex b (synCdm (.cv f)) (synWa
            (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
              (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))))
      p0410
  have p0412 :=
    @gSimp3ll (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
      (.classEq (.cv w) (synCfv (.cv f) (.cv b))) (synWbr (.cv a) (.cv s) (.cv b))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
  have p0413 :=
    @gSimp1 (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
          (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))
  have p0414 :=
    @gSimp2l (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f)))
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
          (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))
  have p0415 := @gF1of (synCdm (.cv f)) (synCrn (.cv f)) (.cv f)
  have p0416 := @gFfvelrn (synCdm (.cv f)) (synCrn (.cv f)) (.cv a) (.cv f)
  have p0417 :=
    @gSylan (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv a) (synCdm (.cv f)))
      (.classMem (synCfv (.cv f) (.cv a)) (synCrn (.cv f))) p0415 p0416
  have p0418 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv a) (synCdm (.cv f)))
      (.classMem (synCfv (.cv f) (.cv a)) (synCrn (.cv f))) p0413 p0414 p0417
  have p0419 :=
    @gEqeltrd
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (.cv z) (synCfv (.cv f) (.cv a)) (synCrn (.cv f)) p0412 p0418
  have p0420 :=
    @gSimp3lr (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
      (.classEq (.cv w) (synCfv (.cv f) (.cv b))) (synWbr (.cv a) (.cv s) (.cv b))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
  have p0421 :=
    @gSimp2r (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f)))
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
          (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))
  have p0422 := @gFfvelrn (synCdm (.cv f)) (synCrn (.cv f)) (.cv b) (.cv f)
  have p0423 :=
    @gSylan (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv b) (synCdm (.cv f)))
      (.classMem (synCfv (.cv f) (.cv b)) (synCrn (.cv f))) p0415 p0422
  have p0424 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv b) (synCdm (.cv f)))
      (.classMem (synCfv (.cv f) (.cv b)) (synCrn (.cv f))) p0413 p0421 p0423
  have p0425 :=
    @gEqeltrd
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (.cv w) (synCfv (.cv f) (.cv b)) (synCrn (.cv f)) p0420 p0424
  have p0426 :=
    @gSimp3r (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
      (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
        (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
      (synWbr (.cv a) (.cv s) (.cv b))
  have p0427 :=
    @gEqcomd
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (.cv z) (synCfv (.cv f) (.cv a)) p0412
  have p0428 := @gF1ocnvfv (synCdm (.cv f)) (synCrn (.cv f)) (.cv a) (.cv z) (.cv f)
  have p0429 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv a) (synCdm (.cv f)))
      (.imp (.classEq (synCfv (.cv f) (.cv a)) (.cv z))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv z)) (.cv a)))
      p0413 p0414 p0428
  have p0430 :=
    @gMpd
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (.classEq (synCfv (.cv f) (.cv a)) (.cv z))
      (.classEq (synCfv (synCcnv (.cv f)) (.cv z)) (.cv a)) p0427 p0429
  have p0431 :=
    @gEqcomd
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (.cv w) (synCfv (.cv f) (.cv b)) p0420
  have p0432 := @gF1ocnvfv (synCdm (.cv f)) (synCrn (.cv f)) (.cv b) (.cv w) (.cv f)
  have p0433 :=
    @gSyl2anc
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv b) (synCdm (.cv f)))
      (.imp (.classEq (synCfv (.cv f) (.cv b)) (.cv w))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv w)) (.cv b)))
      p0413 p0421 p0432
  have p0434 :=
    @gMpd
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (.classEq (synCfv (.cv f) (.cv b)) (.cv w))
      (.classEq (synCfv (synCcnv (.cv f)) (.cv w)) (.cv b)) p0431 p0433
  have p0435 :=
    @gN3brtr4d
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (.cv a) (.cv b) (synCfv (synCcnv (.cv f)) (.cv z))
      (synCfv (synCcnv (.cv f)) (.cv w)) (.cv s) p0426 p0430 p0434
  have p0436 :=
    @gJca31
      (synW3a (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
        (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
            (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b))))
      (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      p0419 p0425 p0435
  have p0437 :=
    @gN3exp (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
          (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))
      (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
          (.classMem (.cv w) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      p0436
  have p0438 :=
    @gRexlimdvv (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
          (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))
      (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
          (.classMem (.cv w) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      a b (synCdm (.cv f)) (synCdm (.cv f)) dv_cache_0048 dv_cache_0054 dv_cache_0055
      dv_cache_0056 dv_cache_0057 dv_cache_0058 p0437
  have p0439 :=
    @gImpbid (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
          (.classMem (.cv w) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      (synWrex a (synCdm (.cv f)) (synWrex b (synCdm (.cv f)) (synWa
            (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
              (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))))
      p0411 p0438
  have p0440 :=
    @gOpabbidv (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
          (.classMem (.cv w) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      (synWrex a (synCdm (.cv f)) (synWrex b (synCdm (.cv f)) (synWa
            (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
              (.classEq (.cv w) (synCfv (.cv f) (.cv b)))) (synWbr (.cv a) (.cv s) (.cv b)))))
      z w dv_cache_0059 dv_cache_0060 p0439
  have p0441 :=
    @gEqeq2d (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
      (synCopab z w (synWrex a (synCdm (.cv f)) (synWrex b (synCdm (.cv f)) (synWa
              (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
                (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
              (synWbr (.cv a) (.cv s) (.cv b))))))
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) p0440
  have p0442 :=
    @gMpbidi (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classEq (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCopab z w (synWa
            (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv s)
              (synCfv (synCcnv (.cv f)) (.cv w))))))
      (.classEq (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCopab z w
          (synWrex a (synCdm (.cv f)) (synWrex b (synCdm (.cv f)) (synWa
                (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
                  (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
                (synWbr (.cv a) (.cv s) (.cv b)))))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      p0382 p0441
  have p0443 :=
    @gF1oiso a b z w (synCdm (.cv f)) (synCrn (.cv f)) (.cv s)
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv f) dv_cache_0061
      dv_cache_0052 dv_cache_0048 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0031
      dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0032 dv_cache_0015 dv_cache_0068
      dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0058 dv_cache_0073
      dv_cache_0074
  have p0444 :=
    @gEx (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classEq (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCopab z w
          (synWrex a (synCdm (.cv f)) (synWrex b (synCdm (.cv f)) (synWa
                (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
                  (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
                (synWbr (.cv a) (.cv s) (.cv b)))))))
      (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0443
  have p0445 :=
    @gSyl9
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classEq (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCopab z w
          (synWrex a (synCdm (.cv f)) (synWrex b (synCdm (.cv f)) (synWa
                (synWa (.classEq (.cv z) (synCfv (.cv f) (.cv a)))
                  (.classEq (.cv w) (synCfv (.cv f) (.cv b))))
                (synWbr (.cv a) (.cv s) (.cv b)))))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0442 p0444
  have p0446 := @gId (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
  have p0447 :=
    @gA1ii
      (.imp (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
        (.imp (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
          (.imp (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) (synWiso (.cv f) (.cv s)
              (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))))))
      (.imp (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))))
      p0445 p0446
  have p0448 :=
    @gPm243d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0447
  have p0449 :=
    @gMpd
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0296 p0448
  have p0450 :=
    @gIsoeq4 (synCdm (.cv f)) (synCrn (.cv f)) (synChnord A) (.cv s)
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv f)
  have p0451 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classEq (synCdm (.cv f)) (synChnord A))
      (synWb (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synChnord A) (synCrn (.cv f))))
      p0293 p0450
  have p0452 :=
    @gMpbid
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synChnord A) (synCrn (.cv f)))
      p0449 p0451
  have p0453 :=
    @gIsoeq2 (synChnord A) (synCrn (.cv f)) (.cv s)
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
      (synClnqord (.cv r) (synChwcn A)) (.cv f)
  have p0454 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))
      (synWb (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synChnord A) (synCrn (.cv f)))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
          (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
          (synCrn (.cv f))))
      p0072 p0453
  have p0455 :=
    @gMpbid
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWiso (.cv f) (.cv s) (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
        (synChnord A) (synCrn (.cv f)))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
        (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
        (synCrn (.cv f)))
      p0452 p0454
  have p0456 :=
    @gJca
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChwcn (synCpw1 (synCpw1 A))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
        (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
        (synCrn (.cv f)))
      p0291 p0455
  have p0471 :=
    @gOp1std (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))
      (.cv u) p0157 p0102
  have p0472 :=
    @gIsoeq3 (synChnord A) (synCfv (synC2nd) (.cv u))
      (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv f)
  have p0473 :=
    @gSyl
      (.classEq (.cv u) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))))
      (.classEq (synCfv (synC1st) (.cv u))
        (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))))
      (synWb (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u)))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
          (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
          (synCfv (synC2nd) (.cv u))))
      p0471 p0472
  have p0488 :=
    @gOp2ndd (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f))
      (.cv u) p0157 p0102
  have p0489 :=
    @gIsoeq5 (synChnord A) (synCfv (synC2nd) (.cv u)) (synCrn (.cv f))
      (synClnqord (.cv r) (synChwcn A))
      (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (.cv f)
  have p0490 :=
    @gSyl
      (.classEq (.cv u) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))))
      (.classEq (synCfv (synC2nd) (.cv u)) (synCrn (.cv f)))
      (synWb (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
          (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
          (synCfv (synC2nd) (.cv u))) (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
          (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
          (synCrn (.cv f))))
      p0488 p0489
  have p0491 :=
    @gBitrd
      (.classEq (.cv u) (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
          (synCrn (.cv f))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
        (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
        (synCfv (synC2nd) (.cv u)))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
        (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
        (synCrn (.cv f)))
      p0473 p0490
  have p0492 :=
    @gRspcev
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
        (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
        (synCrn (.cv f)))
      u
      (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synCrn (.cv f)))
      (synChwcn (synCpw1 (synCpw1 A))) dv_cache_0075 dv_cache_0076 dv_cache_0077 p0491
  have p0493 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (synCop (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
          (synCcom (synCcom (.cv f) (.cv s)) (synCcnv (.cv f))) (synChnord A)
          (synCrn (.cv f))))
      (synWrex u (synChwcn (synCpw1 (synCpw1 A)))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      p0456 p0492
  have p0494 :=
    @gSimpl (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
  have p0495 :=
    @gHncodepw12repdndv v u A dv_cache_0078 dv_cache_0079 dv_cache_0080
      hyp_hninjraisedselfcutalldndv_1
  have p0496 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0494 p0495
  have p0497 :=
    @gNfv
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      v dv_cache_0081
  have p0498 :=
    @gNfri
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      v p0497
  have p0499 :=
    @gSimpl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
  have p0501 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))) p0499 p0494
  have p0502 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
  have p0503 :=
    @gSimpl (.classMem (.cv v) (synChwcn A))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
  have p0504 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (.classMem (.cv v) (synChwcn A)) p0502 p0503
  have p0506 :=
    @gSimpr (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
  have p0507 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      p0499 p0506
  have p0509 :=
    @gSimpr (.classMem (.cv v) (synChwcn A))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
  have p0510 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      p0502 p0509
  have p0511 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      p0507 p0510
  have p0512 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (.classMem (.cv v) (synChwcn A))
      (synWa (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0504 p0511
  have p0513 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv v) (synChwcn A)) (synWa
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      p0501 p0512
  have p0514 :=
    @gSimpr (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv v) (synChwcn A)) (synWa
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
  have p0515 :=
    @gSimpr (.classMem (.cv v) (synChwcn A))
      (synWa (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
  have p0516 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (.cv v) (synChwcn A)) (synWa
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (synWa (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0514 p0515
  have p0517 :=
    @gSimpl
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
  have p0518 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      p0516 p0517
  have p0519 :=
    @gIsof1o (synChnord A) (synCfv (synC2nd) (.cv u))
      (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u)) (.cv f)
  have p0520 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWf1o (.cv f) (synChnord A) (synCfv (synC2nd) (.cv u))) p0518 p0519
  have p0521 := @gF1of (synChnord A) (synCfv (synC2nd) (.cv u)) (.cv f)
  have p0522 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWf1o (.cv f) (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWf (.cv f) (synChnord A) (synCfv (synC2nd) (.cv u))) p0520 p0521
  have p0524 :=
    @gSimpl (.classMem (.cv v) (synChwcn A))
      (synWa (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
  have p0525 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (.cv v) (synChwcn A)) (synWa
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (.classMem (.cv v) (synChwcn A)) p0514 p0524
  have p0526 := @gHwnisoclasselhnordcl A (.cv v) hyp_hninjraisedselfcutalldndv_1
  have p0527 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (.cv v) (synChwcn A))
      (.classMem (synCec (.cv v) (synChwniso A)) (synChnord A)) p0525 p0526
  have p0528 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWf (.cv f) (synChnord A) (synCfv (synC2nd) (.cv u)))
      (.classMem (synCec (.cv v) (synChwniso A)) (synChnord A)) p0522 p0527
  have p0529 :=
    @gFfvelrn (synChnord A) (synCfv (synC2nd) (.cv u))
      (synCec (.cv v) (synChwniso A)) (.cv f)
  have p0530 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (synWf (.cv f) (synChnord A) (synCfv (synC2nd) (.cv u)))
        (.classMem (synCec (.cv v) (synChwniso A)) (synChnord A)))
      (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
        (synCfv (synC2nd) (.cv u)))
      p0528 p0529
  have p0534 :=
    @gSimpr
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
  have p0535 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      p0516 p0534
  have p0536 :=
    @gSimpl (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv v) (synChwcn A)) (synWa
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
  have p0537 := @gHnsicodemap2valclndv v A dv_cache_0079 hyp_hninjraisedselfcutalldndv_1
  have p0538 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (.cv v) (synChwcn A))
      (synWa (.classEq (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
            (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))))) (.classMem
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      p0525 p0537
  have p0539 :=
    @gSimpr
      (.classEq (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwcn (synCpw1 (synCpw1 A))))
  have p0540 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classEq (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
            (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))))) (.classMem
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwcn (synCpw1 (synCpw1 A))))
      p0538 p0539
  have p0541 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwcn (synCpw1 (synCpw1 A))))
      p0536 p0540
  have p0542 := @gPw1ex A hyp_hninjraisedselfcutalldndv_1
  have p0543 := @gPw1ex (synCpw1 A) p0542
  have p0544 :=
    @gHwnisoclasseqbcl (synCpw1 (synCpw1 A)) (.cv u)
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      p0543
  have p0545 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))) (.classMem
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      (synWb (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
            (synChwniso (synCpw1 (synCpw1 A)))))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0541 p0544
  have p0546 :=
    @gMpbird
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      p0535 p0545
  have p0550 := Nominal.mp hyp_hninjraisedselfcutalldndv_1 p0010
  have p0551 :=
    @gSyl6eqel
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.cv r) (synChncodecmpset A) (synCvv) p0007 p0550
  have p0552 := @gHwcnex A hyp_hninjraisedselfcutalldndv_1
  have p0553 :=
    @gJctir
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)) p0551 p0552
  have p0554 := @gLnqordexg (synChwcn A) (.cv r) dv_cache_0001
  have p0555 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synClnqord (.cv r) (synChwcn A)) (synCvv)) p0553 p0554
  have p0556 := @gIdex
  have p0557 :=
    @gDifexg (synClnqord (.cv r) (synChwcn A)) (synCid) (synCvv) (synCvv)
  have p0558 :=
    @gSylancl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (synClnqord (.cv r) (synChwcn A)) (synCvv))
      (.classMem (synCid) (synCvv))
      (.classMem (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)) (synCvv)) p0555
      p0556 p0557
  have p0559 :=
    @gCnvexg (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)) (synCvv)
  have p0560 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)) (synCvv))
      (.classMem (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))) (synCvv))
      p0558 p0559
  have p0561 := @gSnex (synCec (.cv v) (synChwniso A))
  have p0562 :=
    @gImaexg (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
      (synCsn (synCec (.cv v) (synChwniso A))) (synCvv) (synCvv)
  have p0563 :=
    @gSylancl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))) (synCvv))
      (.classMem (synCsn (synCec (.cv v) (synChwniso A))) (synCvv))
      (.classMem (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv v) (synChwniso A)))) (synCvv))
      p0560 p0561 p0562
  have p0564 :=
    @gInexg (synChnord A)
      (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
        (synCsn (synCec (.cv v) (synChwniso A))))
      (synCvv) (synCvv)
  have p0565 :=
    @gSylancr
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (synChnord A) (synCvv))
      (.classMem (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv v) (synChwniso A)))) (synCvv))
      (.classMem (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))) (synCvv))
      p0092 p0563 p0564
  have p0566 :=
    @gResexg (.cv f)
      (synCin (synChnord A)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv v) (synChwniso A)))))
      (synCvv) (synCvv)
  have p0567 :=
    @gSylancr
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (.cv f) (synCvv))
      (.classMem (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))) (synCvv))
      (.classMem (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCvv))
      p0100 p0565 p0566
  have p0568 :=
    @gA1d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCvv))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      p0567
  have p0569 := @gHnqmap1exg A
  have p0570 := Nominal.mp hyp_hninjraisedselfcutalldndv_1 p0569
  have p0571 :=
    (Nominal.classEqRefl
      (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
  have p0572 :=
    (Nominal.classEqRefl
      (synChnwcutfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
  have p0573 := (Nominal.classEqRefl (synChnwcodefn (synCfv (synC1st) (.cv v))))
  have p0575 := @gHwcnweclndv A (.cv v)
  have p0576 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (.cv v) (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v))) p0525
      p0575
  have p0577 :=
    @gBrex (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (synCwe)
  have p0578 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v)))
      (synWa (.classMem (synCfv (synC1st) (.cv v)) (synCvv))
        (.classMem (synCfv (synC2nd) (.cv v)) (synCvv)))
      p0576 p0577
  have p0579 :=
    @gSimpld
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCfv (synC1st) (.cv v)) (synCvv))
      (.classMem (synCfv (synC2nd) (.cv v)) (synCvv)) p0578
  have p0580 := @gResexg (synCid) (synCfv (synC1st) (.cv v)) (synCvv) (synCvv)
  have p0581 :=
    @gSylancr
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCid) (synCvv)) (.classMem (synCfv (synC1st) (.cv v)) (synCvv))
      (.classMem (synCres (synCid) (synCfv (synC1st) (.cv v))) (synCvv)) p0556 p0579
      p0580
  have p0582 := @gImageexg (synCres (synCid) (synCfv (synC1st) (.cv v))) (synCvv)
  have p0583 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCres (synCid) (synCfv (synC1st) (.cv v))) (synCvv))
      (.classMem (synCimage (synCres (synCid) (synCfv (synC1st) (.cv v)))) (synCvv))
      p0581 p0582
  have p0584 := @gCrossex
  have p0587 := @gTxpex (synCid) (synCid) p0556 p0556
  have p0588 := @gCoex (synCcross) (synCtxp (synCid) (synCid)) p0584 p0587
  have p0589 :=
    @gCoexg (synCimage (synCres (synCid) (synCfv (synC1st) (.cv v))))
      (synCcom (synCcross) (synCtxp (synCid) (synCid))) (synCvv) (synCvv)
  have p0590 :=
    @gSylancl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCimage (synCres (synCid) (synCfv (synC1st) (.cv v)))) (synCvv))
      (.classMem (synCcom (synCcross) (synCtxp (synCid) (synCid))) (synCvv))
      (.classMem (synCcom (synCimage (synCres (synCid) (synCfv (synC1st) (.cv v))))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCvv))
      p0583 p0588 p0589
  have p0592 :=
    @gTxpexg
      (synCcom (synCimage (synCres (synCid) (synCfv (synC1st) (.cv v))))
        (synCcom (synCcross) (synCtxp (synCid) (synCid))))
      (synCid) (synCvv) (synCvv)
  have p0593 :=
    @gSylancl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCcom (synCimage (synCres (synCid) (synCfv (synC1st) (.cv v))))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCvv))
      (.classMem (synCid) (synCvv))
      (.classMem (synCtxp
          (synCcom (synCimage (synCres (synCid) (synCfv (synC1st) (.cv v))))
            (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid)) (synCvv))
      p0590 p0556 p0592
  have p0594 :=
    @gSyl5eqel
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synChnwcodefn (synCfv (synC1st) (.cv v)))
      (synCtxp (synCcom (synCimage (synCres (synCid) (synCfv (synC1st) (.cv v))))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))
      (synCvv) p0573 p0593
  have p0595 :=
    (Nominal.classEqRefl
      (synChnwsegfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
  have p0597 :=
    @gSimprd
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCfv (synC1st) (.cv v)) (synCvv))
      (.classMem (synCfv (synC2nd) (.cv v)) (synCvv)) p0578
  have p0598 := @gResexg (synCid) (synCfv (synC2nd) (.cv v)) (synCvv) (synCvv)
  have p0599 :=
    @gSylancr
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCid) (synCvv)) (.classMem (synCfv (synC2nd) (.cv v)) (synCvv))
      (.classMem (synCres (synCid) (synCfv (synC2nd) (.cv v))) (synCvv)) p0556 p0597
      p0598
  have p0600 := @gImageexg (synCres (synCid) (synCfv (synC2nd) (.cv v))) (synCvv)
  have p0601 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCres (synCid) (synCfv (synC2nd) (.cv v))) (synCvv))
      (.classMem (synCimage (synCres (synCid) (synCfv (synC2nd) (.cv v)))) (synCvv))
      p0599 p0600
  have p0603 := @gDifexg (synCfv (synC1st) (.cv v)) (synCid) (synCvv) (synCvv)
  have p0604 :=
    @gSylancl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCfv (synC1st) (.cv v)) (synCvv)) (.classMem (synCid) (synCvv))
      (.classMem (synCdif (synCfv (synC1st) (.cv v)) (synCid)) (synCvv)) p0579 p0556
      p0603
  have p0605 := @gCnvexg (synCdif (synCfv (synC1st) (.cv v)) (synCid)) (synCvv)
  have p0606 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCdif (synCfv (synC1st) (.cv v)) (synCid)) (synCvv))
      (.classMem (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))) (synCvv))
      p0604 p0605
  have p0607 :=
    @gImageexg (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))) (synCvv)
  have p0608 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))) (synCvv))
      (.classMem (synCimage (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))))
        (synCvv))
      p0606 p0607
  have p0609 :=
    @gCoexg (synCimage (synCres (synCid) (synCfv (synC2nd) (.cv v))))
      (synCimage (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))) (synCvv)
      (synCvv)
  have p0610 :=
    @gSyl2anc
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCimage (synCres (synCid) (synCfv (synC2nd) (.cv v)))) (synCvv))
      (.classMem (synCimage (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))))
        (synCvv))
      (.classMem (synCcom (synCimage (synCres (synCid) (synCfv (synC2nd) (.cv v))))
          (synCimage (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))))) (synCvv))
      p0601 p0608 p0609
  have p0611 :=
    @gSyl5eqel
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synChnwsegfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
      (synCcom (synCimage (synCres (synCid) (synCfv (synC2nd) (.cv v))))
        (synCimage (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))))
      (synCvv) p0595 p0610
  have p0612 :=
    @gCoexg (synChnwcodefn (synCfv (synC1st) (.cv v)))
      (synChnwsegfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))) (synCvv)
      (synCvv)
  have p0613 :=
    @gSyl2anc
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synChnwcodefn (synCfv (synC1st) (.cv v))) (synCvv))
      (.classMem (synChnwsegfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
        (synCvv))
      (.classMem (synCcom (synChnwcodefn (synCfv (synC1st) (.cv v)))
          (synChnwsegfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))) (synCvv))
      p0594 p0611 p0612
  have p0614 :=
    @gSyl5eqel
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synChnwcutfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
      (synCcom (synChnwcodefn (synCfv (synC1st) (.cv v)))
        (synChnwsegfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      (synCvv) p0572 p0613
  have p0615 := @gPw1exg (synCfv (synC2nd) (.cv v)) (synCvv)
  have p0616 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCfv (synC2nd) (.cv v)) (synCvv))
      (.classMem (synCpw1 (synCfv (synC2nd) (.cv v))) (synCvv)) p0597 p0615
  have p0617 :=
    @gResexg (synChnwcutfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
      (synCpw1 (synCfv (synC2nd) (.cv v))) (synCvv) (synCvv)
  have p0618 :=
    @gSyl2anc
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synChnwcutfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
        (synCvv))
      (.classMem (synCpw1 (synCfv (synC2nd) (.cv v))) (synCvv))
      (.classMem (synCres
          (synChnwcutfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
          (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCvv))
      p0614 p0616 p0617
  have p0619 :=
    @gSyl5eqel
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
      (synCres (synChnwcutfn (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
        (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCvv) p0571 p0618
  have p0620 :=
    @gSiexg (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
      (synCvv)
  have p0621 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
        (synCvv))
      (.classMem (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))) (synCvv))
      p0619 p0620
  have p0622 :=
    @gCoexg (synChnqmap1 A)
      (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      (synCvv) (synCvv)
  have p0623 :=
    @gSylancr
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synChnqmap1 A) (synCvv))
      (.classMem (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))) (synCvv))
      (.classMem (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
        (synCvv))
      p0570 p0621 p0622
  have p0624 :=
    @gCoexg
      (synCres (.cv f) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))))
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
      (synCvv) (synCvv)
  have p0625 :=
    @gEx
      (.classMem (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCvv))
      (.classMem (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
        (synCvv))
      (.classMem (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCvv))
      p0624
  have p0626 :=
    @gSyl5
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
        (synCvv))
      (.classMem (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCvv))
      (.classMem (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCvv))
      p0623 p0625
  have p0627 :=
    @gSyl6
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCvv))
      (.imp (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWa (.classMem (.cv v) (synChwcn A)) (synWa
              (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
                (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
              (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))) (.classMem
          (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCvv)))
      p0568 p0626
  have p0628 :=
    @gPm243d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCvv))
      p0627
  have p0629 :=
    @gIsset k
      (synCcom (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))))
      dv_cache_0082
  have p0630 :=
    @gSyl6ib
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCvv))
      (synWex k (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v))))))))
      p0628 p0629
  have p0631 :=
    Nominal.ax17
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      k dv_cache_0083
  have p0638 :=
    @gHnwcutambstrictsegresisomraliasdndv v A r dv_cache_0002 dv_cache_0079 dv_cache_0084
      hyp_hninjraisedselfcutalldndv_1
  have p0639 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classEq (.cv r) (synChncodecmpset A))
      (.imp (.classMem (.cv v) (synChwcn A)) (synWiso (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
          (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))))
      p0007 p0638
  have p0640 :=
    @gSyl5
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (.cv v) (synChwcn A))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv v))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))))
      p0525 p0639
  have p0641 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (.classMem (synCec (.cv v) (synChwniso A)) (synChnord A)) p0518 p0527
  have p0642 :=
    @gIsostrictsegresclndv (synCec (.cv v) (synChwniso A)) (synChnord A)
      (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
      (synCfv (synC2nd) (.cv u)) (.cv f)
  have p0643 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u)))
        (.classMem (synCec (.cv v) (synChwniso A)) (synChnord A)))
      (synWiso (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A))))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
        (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      p0641 p0642
  have p0644 :=
    @g_pm3_2
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv v))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))))
      (synWiso (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A))))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
        (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
  have p0645 :=
    @gSyl5
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A))))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
        (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv v))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))))
      (synWa (synWiso (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
          (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synWiso (synCres (.cv f)
            (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
          (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0643 p0644
  have p0646 :=
    @gSyl6
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv v))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))))
      (.imp (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWa (.classMem (.cv v) (synChwcn A)) (synWa
              (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
                (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
              (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))) (synWa
          (synWiso (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
            (synCsi (synCsi (synCfv (synC1st) (.cv v))))
            (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv v) (synChwniso A)))))))
            (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synWiso (synCres (.cv f)
              (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A))))))
            (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv v) (synChwniso A)))))))
            (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
                (synCin (synCfv (synC2nd) (.cv u))
                  (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                    (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
            (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))))
      p0640 p0645
  have p0647 :=
    @gPm243d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (synWiso (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
          (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synWiso (synCres (.cv f)
            (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
          (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0646
  have p0648 :=
    @gIsotr (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCin (synChnord A)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv v) (synChwniso A)))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synCsi (synCsi (synCfv (synC1st) (.cv v))))
      (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      (synCres (.cv f) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv v) (synChwniso A))))))
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
  have p0649 :=
    @gSyl6
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (synWiso (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))))
          (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synWiso (synCres (.cv f)
            (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A))))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
          (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v))))))
        (synCsi (synCsi (synCfv (synC1st) (.cv v)))) (synCin (synCfv (synC1st) (.cv u))
          (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      p0647 p0648
  have p0650 :=
    @gSimpl
      (.classEq (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwcn (synCpw1 (synCpw1 A))))
  have p0651 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classEq (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
            (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))))) (.classMem
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      (.classEq (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))))
      p0538 p0650
  have p0652 := @gFvex (.cv v) (synC1st)
  have p0653 := @gSiex (synCfv (synC1st) (.cv v)) p0652
  have p0654 := @gSiex (synCsi (synCfv (synC1st) (.cv v))) p0653
  have p0655 := @gFvex (.cv v) (synC2nd)
  have p0656 := @gPw1ex (synCfv (synC2nd) (.cv v)) p0655
  have p0657 := @gPw1ex (synCpw1 (synCfv (synC2nd) (.cv v))) p0656
  have p0658 :=
    @gOp1std (synCsi (synCsi (synCfv (synC1st) (.cv v))))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      p0654 p0657
  have p0659 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))))
      (.classEq (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCsi (synCsi (synCfv (synC1st) (.cv v)))))
      p0651 p0658
  have p0660 :=
    @gEqcomd
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCsi (synCsi (synCfv (synC1st) (.cv v)))) p0659
  have p0661 :=
    @gIsoeq2 (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synCsi (synCsi (synCfv (synC1st) (.cv v))))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCcom (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))))
  have p0662 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCsi (synCsi (synCfv (synC1st) (.cv v)))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (synWb (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v))))))
          (synCsi (synCsi (synCfv (synC1st) (.cv v)))) (synCin (synCfv (synC1st) (.cv u))
            (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))) (synWiso
          (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0660 p0661
  have p0663 :=
    @gMpbidi
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v))))))
        (synCsi (synCsi (synCfv (synC1st) (.cv v)))) (synCin (synCfv (synC1st) (.cv u))
          (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      p0649 p0662
  have p0664 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
        (synCfv (synC2nd) (.cv u)))
      p0536 p0530
  have p0665 :=
    @gHnwcutcodepartsclndv u (synCpw1 (synCpw1 A))
      (synCfv (.cv f) (synCec (.cv v) (synChwniso A))) dv_cache_0085
  have p0666 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
          (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))) (.classEq
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0664 p0665
  have p0667 :=
    @gSimpl
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
  have p0668 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))) (.classEq
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))))
      p0666 p0667
  have p0669 :=
    @gEqcomd
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0668
  have p0670 :=
    @gIsoeq3 (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synCcom (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))))
  have p0671 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
        (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synWb (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))) (synWiso
          (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0669 p0670
  have p0672 :=
    @gMpbidi
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      p0663 p0671
  have p0679 :=
    @gOp2ndd (synCsi (synCsi (synCfv (synC1st) (.cv v))))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      p0654 p0657
  have p0680 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))))
      (.classEq (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0651 p0679
  have p0681 :=
    @gEqcomd
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) p0680
  have p0682 :=
    @gIsoeq4 (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synCcom (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))))
  have p0683 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (synWb (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))) (synWiso
          (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0681 p0682
  have p0684 :=
    @gMpbidi
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      p0672 p0683
  have p0685 :=
    @gSimpr
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
  have p0686 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))) (.classEq
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      p0666 p0685
  have p0687 :=
    @gEqcomd
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      p0686
  have p0688 :=
    @gIsoeq5
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synCcom (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))))
  have p0689 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synWb (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))) (synWiso
          (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      p0687 p0688
  have p0690 :=
    @gMpbidi
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      p0684 p0689
  have p0691 :=
    @gA1dd
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))))
      p0690
  have p0692 :=
    @gIsoeq1
      (synCfv (synC2nd) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synCcom (synCres (.cv f) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))))
      (.cv k)
  have p0693 :=
    @gBiimprd
      (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))))
      (synWiso (.cv k) (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      p0692
  have p0694 :=
    @gA2i
      (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))))
      (synWiso (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synWiso (.cv k) (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      p0693
  have p0695 :=
    @gSyl6
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.imp (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v))))))) (synWiso (synCcom (synCres (.cv f)
              (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v)))))) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (.imp (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v))))))) (synWiso (.cv k) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      p0691 p0694
  have p0696 :=
    @gAlimdv
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.imp (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v))))))) (synWiso (.cv k) (synCfv (synC1st)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      k dv_cache_0086 p0695
  have p0697 :=
    @gSyl5
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.all k (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWa (.classMem (.cv v) (synChwcn A)) (synWa
              (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
                (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
              (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.all k (.imp (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
                (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                    (synCfv (synC2nd) (.cv v))))))) (synWiso (.cv k) (synCfv (synC1st)
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0631 p0696
  have p0698 :=
    @gExim
      (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv v)))))))
      (synWiso (.cv k) (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      k
  have p0699 :=
    @gSyl6
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.all k (.imp (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
                (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                    (synCfv (synC2nd) (.cv v))))))) (synWiso (.cv k) (synCfv (synC1st)
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      (.imp (synWex k (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
                (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                    (synCfv (synC2nd) (.cv v)))))))) (synWex k (synWiso (.cv k)
            (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0697 p0698
  have p0700 :=
    @gMpdd
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWex k (.classEq (.cv k) (synCcom (synCres (.cv f) (synCin (synChnord A) (synCima
                  (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv v) (synChwniso A)))))) (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv v))
                  (synCfv (synC2nd) (.cv v))))))))
      (synWex k (synWiso (.cv k) (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      p0630 p0699
  have p0701 :=
    @gHnwcutcodeambientclndv u (synCpw1 (synCpw1 A))
      (synCfv (.cv f) (synCec (.cv v) (synChwniso A))) dv_cache_0085
  have p0702 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
          (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
        (synChwcn (synCpw1 (synCpw1 A))))
      p0664 p0701
  have p0703 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
        (synChwcn (synCpw1 (synCpw1 A))))
      p0540 p0702
  have p0704 :=
    @gHwnisodirectisobclndv (synCpw1 (synCpw1 A))
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
      k dv_cache_0087 dv_cache_0088 dv_cache_0089
  have p0705 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwcn (synCpw1 (synCpw1 A)))) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      (synWb (synWbr (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synWex k (synWiso (.cv k)
            (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))))
      p0703 p0704
  have p0706 :=
    @gBiimprd
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWbr (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synWex k (synWiso (.cv k) (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      p0705
  have p0707 :=
    @gSylcom
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWex k (synWiso (.cv k) (synCfv (synC1st) (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))) (synCfv (synC2nd)
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      (synWbr (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      p0700 p0706
  have p0710 :=
    @gHwnisoclasseqbcl (synCpw1 (synCpw1 A))
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
      p0543
  have p0711 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwcn (synCpw1 (synCpw1 A)))) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      (synWb (.classEq (synCec (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
            (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
            (synChwniso (synCpw1 (synCpw1 A))))) (synWbr
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      p0703 p0710
  have p0712 :=
    @gBiimprd
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCec (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      (synWbr (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      p0711
  have p0713 :=
    @gSylcom
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWbr (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (.classEq (synCec (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      p0707 p0712
  have p0714 :=
    @gEqeq2
      (synCec (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwniso (synCpw1 (synCpw1 A))))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
        (synChwniso (synCpw1 (synCpw1 A))))
      (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
  have p0715 :=
    @gSyl6
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCec (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      (synWb (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
            (synChwniso (synCpw1 (synCpw1 A)))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
            (synChwniso (synCpw1 (synCpw1 A))))))
      p0713 p0714
  have p0716 :=
    @gBi1
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwniso (synCpw1 (synCpw1 A)))))
  have p0717 :=
    @gSyl6
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWb (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
            (synChwniso (synCpw1 (synCpw1 A)))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
            (synChwniso (synCpw1 (synCpw1 A))))))
      (.imp (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
            (synChwniso (synCpw1 (synCpw1 A)))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
            (synChwniso (synCpw1 (synCpw1 A))))))
      p0715 p0716
  have p0718 :=
    @gMpdi
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      p0546 p0717
  have p0719 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
        (synChwcn (synCpw1 (synCpw1 A))))
      p0536 p0702
  have p0722 :=
    @gHwnisoclasseqbcl (synCpw1 (synCpw1 A)) (.cv u)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
      p0543
  have p0723 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      (synWb (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
            (synChwniso (synCpw1 (synCpw1 A)))))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      p0719 p0722
  have p0724 :=
    @gMpbidi
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      p0718 p0723
  have p0725 :=
    @g_pm3_2
      (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
        (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
  have p0726 :=
    @gSyl9
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
        (synCfv (synC2nd) (.cv u)))
      (synWa (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
          (synCfv (synC2nd) (.cv u))) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      p0724 p0725
  have p0727 :=
    @gSyl5
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
        (synCfv (synC2nd) (.cv u)))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.imp (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWa (.classMem (.cv v) (synChwcn A)) (synWa
              (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
                (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
              (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))) (synWa
          (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
            (synCfv (synC2nd) (.cv u))) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))))
      p0530 p0726
  have p0728 :=
    @gPm243d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
          (synCfv (synC2nd) (.cv u))) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      p0727
  have p0729 :=
    @gHnwcutcodeeq3 (.cv x) (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
      (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) dv_cache_0090
  have p0730 :=
    @gBreq2d (.classEq (.cv x) (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))
      (.cv u) (synChwniso (synCpw1 (synCpw1 A))) p0729
  have p0731 :=
    @gRspcev
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))))
      x (synCfv (.cv f) (synCec (.cv v) (synChwniso A))) (synCfv (synC2nd) (.cv u))
      dv_cache_0091 dv_cache_0092 dv_cache_0093 p0730
  have p0732 :=
    @gSyl6
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (.classMem (synCfv (.cv f) (synCec (.cv v) (synChwniso A)))
          (synCfv (synC2nd) (.cv u))) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCfv (.cv f) (synCec (.cv v) (synChwniso A))))))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0728 p0731
  have p0733 :=
    @gSyl5
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv v) (synChwcn A)) (synWa
            (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
              (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0513 p0732
  have p0734 :=
    @gExp4d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv v) (synChwcn A))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0733
  have p0735 :=
    @gAlimdv
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (.imp (.classMem (.cv v) (synChwcn A)) (.imp
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
          (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))))))
      v dv_cache_0094 p0734
  have p0736 :=
    @gSyl5
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (.all v (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
          (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A))
            (synCfv (synC1st) (.cv u)) (synChnord A) (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.all v (.imp (.classMem (.cv v) (synChwcn A)) (.imp
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
            (synWrex x (synCfv (synC2nd) (.cv u))
              (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x)))))))
      p0498 p0735
  have p0737 :=
    (Nominal.biimpRefl (synWral v (synChwcn A) (.imp
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
          (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)))))))
  have p0738 :=
    @gSyl6ibr
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (.all v (.imp (.classMem (.cv v) (synChwcn A)) (.imp
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
            (synWrex x (synCfv (synC2nd) (.cv u))
              (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x)))))))
      (synWral v (synChwcn A) (.imp (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
          (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))))))
      p0736 p0737
  have p0739 :=
    @gNfv
      (synWrex x (synCfv (synC2nd) (.cv u))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      v dv_cache_0095
  have p0740 :=
    @gR1923
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      v (synChwcn A) p0739
  have p0741 :=
    @gSyl6ib
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (synWral v (synChwcn A) (.imp (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
          (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))))))
      (.imp (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
        (synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      p0738 p0740
  have p0742 :=
    @gMpdi
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0496 p0741
  have p0743 :=
    @gExp3a
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0742
  have p0744 :=
    @gReximdvai
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
        (synChnord A) (synCfv (synC2nd) (.cv u)))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      u (synChwcn (synCpw1 (synCpw1 A))) dv_cache_0096 p0743
  have p0745 :=
    @gMpd
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWrex u (synChwcn (synCpw1 (synCpw1 A)))
        (synWiso (.cv f) (synClnqord (.cv r) (synChwcn A)) (synCfv (synC1st) (.cv u))
          (synChnord A) (synCfv (synC2nd) (.cv u))))
      (synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      p0493 p0744
  exact p0745


end NFChoice.DirectNominalPrf.WPPReplay
