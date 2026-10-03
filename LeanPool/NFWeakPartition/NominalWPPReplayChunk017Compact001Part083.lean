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

@[expose]
noncomputable def g_hninjraisedselfcutalldndv (x : Var) (u : Var) (A : Class) (f : Var)
    (s : Var) (r : Var) (_dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (_dv_A_s : s ∉ A.fv)
    (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (_dv_f_r : f ≠ r) (_dv_f_s : f ≠ s)
    (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) (_dv_r_s : r ≠ s) (dv_r_u : r ≠ u) (dv_r_x : r ≠ x)
    (dv_s_u : s ≠ u) (dv_s_x : s ≠ x) (dv_u_x : u ≠ x)
    (hyp_hninjraisedselfcutalldndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
        (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
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
  have dv_cache_0001 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv := by
    exact
      (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by
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
  have dv_cache_0009 : b ∉ ((syn_ccnv (.cv f))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (.cv x) (.cv y))
            (syn_wbr (.cv a) (syn_cwe) (.cv y)))
          (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (.cv x)))).fv :=
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
  have dv_cache_0011 : x ∉ ((syn_crn (.cv f))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
            (syn_wbr (.cv a) (syn_cwe) (.cv y)))
          (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))))).fv :=
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
  have dv_cache_0013 : y ∉ ((syn_chnord A)).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
            (syn_wbr (.cv a) (syn_cwe) (syn_chnord A)))
          (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
            (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))
          (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv s)) (syn_cwe) (syn_crn (.cv f))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (.cv f)) (.cv x) (.cv y))
          (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cxp (.cv x) (.cv x))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
          (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
            (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
          (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
            (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
          (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
            (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))).fv :=
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
  have dv_cache_0023 : z ∉ ((syn_ccom (.cv f) (.cv s))).fv :=
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
  have dv_cache_0024 : z ∉ ((syn_ccnv (.cv f))).fv :=
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
      ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))).fv :=
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
  have dv_cache_0026 : z ∉ ((Wff.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))).fv :=
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
  have dv_cache_0027 : z ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv :=
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
      ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y))).fv :=
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
  have dv_cache_0029 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv :=
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
      ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))).fv :=
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
  have dv_cache_0034 : w ∉ ((Wff.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))).fv :=
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
  have dv_cache_0035 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv y))).fv :=
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
      ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y)))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
            (.classMem (.cv y) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
            (.classMem (.cv y) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y))))).fv :=
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
    x ∉ ((syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))).fv :=
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
    y ∉ ((syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))).fv :=
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
      ((syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))).fv :=
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
      ((syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))).fv :=
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
      ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))).fv :=
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
      ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))).fv :=
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
  have dv_cache_0047 : b ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv w))).fv :=
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
  have dv_cache_0048 : b ∉ ((syn_cdm (.cv f))).fv :=
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
      ((syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
            (.classEq (.cv w) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w))))).fv :=
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
    b ∉ ((Wff.classEq (.cv a) (syn_cfv (syn_ccnv (.cv f)) (.cv z)))).fv :=
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
  have dv_cache_0051 : a ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv z))).fv :=
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
  have dv_cache_0052 : a ∉ ((syn_cdm (.cv f))).fv :=
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
      ((syn_wrex b (syn_cdm (.cv f)) (syn_wa (syn_wa
              (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
              (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s) (.cv b))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w))))).fv :=
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
  have dv_cache_0056 : a ∉ ((syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))).fv :=
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
  have dv_cache_0057 : b ∉ ((syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))).fv :=
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
  have dv_cache_0059 : z ∉ ((syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))).fv :=
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
  have dv_cache_0060 : w ∉ ((syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))).fv :=
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
  have dv_cache_0061 : w ∉ ((syn_cdm (.cv f))).fv :=
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
  have dv_cache_0062 : z ∉ ((syn_cdm (.cv f))).fv :=
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
  have dv_cache_0063 : a ∉ ((syn_crn (.cv f))).fv :=
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
  have dv_cache_0064 : b ∉ ((syn_crn (.cv f))).fv :=
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
      ((syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f)))).fv :=
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
  have dv_cache_0076 : u ∉ ((syn_chwcn (syn_cpw1 (syn_cpw1 A)))).fv :=
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
      ((syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
          (syn_crn (.cv f)))).fv :=
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
      ((syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
      ((syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v))))))).fv :=
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
      ((syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
              (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
                (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
              (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))).fv :=
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
  have dv_cache_0085 : u ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
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
      ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))).fv :=
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
  have dv_cache_0087 : k ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
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
      ((syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))).fv :=
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
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))).fv :=
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
  have dv_cache_0090 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv :=
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
      (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
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
                  (show Disjoint (({ x } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0091 : x ∉ ((syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))).fv :=
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
  have dv_cache_0092 : x ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv :=
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
      ((syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))).fv :=
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
      ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))).fv :=
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
      ((syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
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
      ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))).fv :=
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
    @g_simpl (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))))
  have p0001 := @g_f1f1orn (syn_chnord A) (syn_cpw1 (syn_cpw1 A)) (.cv f)
  have p0002 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (syn_wf1o (.cv f) (syn_chnord A) (syn_crn (.cv f))) p0000 p0001
  have p0003 := @g_f1ocnv (syn_chnord A) (syn_crn (.cv f)) (.cv f)
  have p0004 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (.cv f) (syn_chnord A) (syn_crn (.cv f)))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A)) p0002 p0003
  have p0005 :=
    @g_simpr (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))))
  have p0006 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))))
      (.classEq (.cv r) (syn_chncodecmpset A)) p0005 p0006
  have p0008 :=
    @g_jctil
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem A (syn_cvv)) p0007
      hyp_hninjraisedselfcutalldndv_1
  have p0009 := @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0010 := @g_hncodecmpsetexg A
  have p0011 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0009 p0010
  have p0012 := @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0013 :=
    @g_eleq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_cvv) p0012
  have p0014 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0011
      p0013
  have p0016 := @g_hwcnexg A
  have p0017 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0009 p0016
  have p0018 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0014 p0017
  have p0020 := @g_hncodecmpsetrefndv A
  have p0021 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
      p0009 p0020
  have p0023 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) p0012
  have p0024 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0021 p0023
  have p0026 := @g_hncodecmpsettransndv A
  have p0027 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))
      p0009 p0026
  have p0029 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_ctrans) p0012
  have p0030 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0027 p0029
  have p0031 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
      (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) p0024 p0030
  have p0033 := @g_hncodecmpsetconnexndv A
  have p0034 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))
      p0009 p0033
  have p0036 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cconnex) p0012
  have p0037 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0034 p0036
  have p0038 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
        (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
      (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)) p0031 p0037
  have p0039 := @g_hncodecmpsetssxpndv A
  have p0040 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) p0039
  have p0042 :=
    @g_sseq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0012
  have p0043 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0040 p0042
  have p0044 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
          (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
        (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
      (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0038 p0043
  have p0045 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
            (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
          (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
        (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      p0018 p0044
  have p0047 := @g_hncodecmpstrictfrndv A
  have p0048 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv))
      (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (syn_cfound) (syn_chwcn A))
      p0009 p0047
  have p0051 :=
    @g_cnveqd (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) p0012
  have p0052 :=
    @g_difeq12d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_ccnv (.cv r)) (syn_ccnv (syn_chncodecmpset A))
      p0012 p0051
  have p0053 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_cdif (.cv r) (syn_ccnv (.cv r)))
      (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_chwcn A)
      (syn_cfound) p0052
  have p0054 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A))
      (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (syn_cfound) (syn_chwcn A))
      p0048 p0053
  have p0055 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
              (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
            (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
          (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))))
      (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A)) p0045
      p0054
  have p0056 := @g_lnqordwe (syn_chwcn A) (.cv r) dv_cache_0001
  have p0057 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
          (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
                (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
              (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
            (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))))
        (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A)))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_clnquo (.cv r) (syn_chwcn A)))
      p0055 p0056
  have p0059 := @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0060 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0012 p0059
  have p0062 := @g_hncodecmplnkerndv A
  have p0063 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem A (syn_cvv))
      (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0009 p0062
  have p0064 :=
    @g_eqtrd (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0060 p0063
  have p0065 := @g_hnordlnquoeqimndv A r dv_cache_0002
  have p0066 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
      (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_chnord A)) p0064 p0065
  have p0067 :=
    @g_breq2d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_clnquo (.cv r) (syn_chwcn A)) (syn_chnord A)
      (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) p0066
  have p0068 :=
    @g_mpbid (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_clnquo (.cv r) (syn_chwcn A)))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0057 p0067
  have p0069 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0008 p0068
  have p0071 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))
  have p0072 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))))
      (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))) p0005 p0071
  have p0073 :=
    @g_breq1d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_chnord A) (syn_cwe) p0072
  have p0074 :=
    @g_mpbird
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
      (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0069 p0073
  have p0075 :=
    @g_jca
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) p0004 p0074
  have p0076 := @g_vex s
  have p0077 := @g_biid (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
  have p0078 :=
    @g_a1i
      (syn_wb (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A)))
      (.classEq (.cv a) (.cv s)) p0077
  have p0079 := @g_id (.classEq (.cv a) (.cv s))
  have p0080 :=
    @g_breq1d (.classEq (.cv a) (.cv s)) (.cv a) (.cv s) (syn_chnord A) (syn_cwe) p0079
  have p0081 :=
    @g_anbi12d (.classEq (.cv a) (.cv s))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wbr (.cv a) (syn_cwe) (syn_chnord A))
      (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) p0078 p0080
  have p0083 :=
    @g_coeq2d (.classEq (.cv a) (.cv s)) (.cv a) (.cv s) (syn_ccnv (syn_ccnv (.cv f)))
      p0079
  have p0084 :=
    @g_coeq1d (.classEq (.cv a) (.cv s)) (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv a))
      (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv s)) (syn_ccnv (.cv f)) p0083
  have p0085 := (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)))
  have p0086 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (syn_ccnv (.cv f))) p0085
  have p0087 := (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (.cv f)) (.cv s)))
  have p0088 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv s)) (syn_ccnv (.cv f))) p0087
  have p0089 :=
    @g_n_3eqtr3g (.classEq (.cv a) (.cv s))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (syn_ccnv (.cv f)))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv s)) (syn_ccnv (.cv f)))
      (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
      p0084 p0086 p0088
  have p0090 :=
    @g_breq1d (.classEq (.cv a) (.cv s)) (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
      (syn_cpwpull (syn_ccnv (.cv f)) (.cv s)) (syn_crn (.cv f)) (syn_cwe) p0089
  have p0091 :=
    @g_imbi12d (.classEq (.cv a) (.cv s))
      (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wbr (.cv a) (syn_cwe) (syn_chnord A)))
      (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f)))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv s)) (syn_cwe) (syn_crn (.cv f))) p0081
      p0090
  have p0092 := @g_hnordex A hyp_hninjraisedselfcutalldndv_1
  have p0093 := @g_f1oeq3 (.cv y) (syn_chnord A) (syn_crn (.cv f)) (syn_ccnv (.cv f))
  have p0094 := @g_id (.classEq (.cv y) (syn_chnord A))
  have p0095 :=
    @g_breq2d (.classEq (.cv y) (syn_chnord A)) (.cv y) (syn_chnord A) (.cv a) (syn_cwe)
      p0094
  have p0096 :=
    @g_anbi12d (.classEq (.cv y) (syn_chnord A))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wbr (.cv a) (syn_cwe) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (syn_chnord A)) p0093
      p0095
  have p0097 :=
    @g_biid (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f)))
  have p0098 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f)))
        (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))))
      (.classEq (.cv y) (syn_chnord A)) p0097
  have p0099 :=
    @g_imbi12d (.classEq (.cv y) (syn_chnord A))
      (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
        (syn_wbr (.cv a) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wbr (.cv a) (syn_cwe) (syn_chnord A)))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f)))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))) p0096
      p0098
  have p0100 := @g_vex f
  have p0101 := @g_rnexg (.cv f) (syn_cvv)
  have p0102 := Nominal.mp p0100 p0101
  have p0103 := @g_f1oeq2 (.cv x) (syn_crn (.cv f)) (.cv y) (syn_ccnv (.cv f))
  have p0104 := @g_biid (syn_wbr (.cv a) (syn_cwe) (.cv y))
  have p0105 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv a) (syn_cwe) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (.cv y)))
      (.classEq (.cv x) (syn_crn (.cv f))) p0104
  have p0106 :=
    @g_anbi12d (.classEq (.cv x) (syn_crn (.cv f)))
      (syn_wf1o (syn_ccnv (.cv f)) (.cv x) (.cv y))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
      (syn_wbr (.cv a) (syn_cwe) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (.cv y)) p0103 p0105
  have p0107 := @g_id (.classEq (.cv x) (syn_crn (.cv f)))
  have p0108 :=
    @g_breq2d (.classEq (.cv x) (syn_crn (.cv f))) (.cv x) (syn_crn (.cv f))
      (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) p0107
  have p0109 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (.cv f)))
      (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (.cv x) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
        (syn_wbr (.cv a) (syn_cwe) (.cv y)))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (.cv x))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))) p0106
      p0108
  have p0111 := @g_cnvexg (.cv f) (syn_cvv)
  have p0112 := Nominal.mp p0100 p0111
  have p0113 := @g_f1oeq1 (.cv x) (.cv y) (.cv b) (syn_ccnv (.cv f))
  have p0115 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv a) (syn_cwe) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (.cv y)))
      (.classEq (.cv b) (syn_ccnv (.cv f))) p0104
  have p0116 :=
    @g_anbi12d (.classEq (.cv b) (syn_ccnv (.cv f))) (syn_wf1o (.cv b) (.cv x) (.cv y))
      (syn_wf1o (syn_ccnv (.cv f)) (.cv x) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (.cv y))
      (syn_wbr (.cv a) (syn_cwe) (.cv y)) p0113 p0115
  have p0117 := @g_id (.classEq (.cv b) (syn_ccnv (.cv f)))
  have p0118 :=
    @g_cnveqd (.classEq (.cv b) (syn_ccnv (.cv f))) (.cv b) (syn_ccnv (.cv f)) p0117
  have p0119 :=
    @g_coeq1d (.classEq (.cv b) (syn_ccnv (.cv f))) (syn_ccnv (.cv b))
      (syn_ccnv (syn_ccnv (.cv f))) (.cv a) p0118
  have p0121 :=
    @g_coeq12d (.classEq (.cv b) (syn_ccnv (.cv f))) (syn_ccom (syn_ccnv (.cv b)) (.cv a))
      (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv b) (syn_ccnv (.cv f)) p0119
      p0117
  have p0122 := (Nominal.classEqRefl (syn_cpwpull (.cv b) (.cv a)))
  have p0123 :=
    @g_eqcomi (syn_cpwpull (.cv b) (.cv a))
      (syn_ccom (syn_ccom (syn_ccnv (.cv b)) (.cv a)) (.cv b)) p0122
  have p0126 :=
    @g_n_3eqtr3g (.classEq (.cv b) (syn_ccnv (.cv f)))
      (syn_ccom (syn_ccom (syn_ccnv (.cv b)) (.cv a)) (.cv b))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (syn_ccnv (.cv f)))
      (syn_cpwpull (.cv b) (.cv a)) (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) p0121 p0123
      p0086
  have p0127 :=
    @g_breq1d (.classEq (.cv b) (syn_ccnv (.cv f))) (syn_cpwpull (.cv b) (.cv a))
      (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (.cv x) (syn_cwe) p0126
  have p0128 :=
    @g_imbi12d (.classEq (.cv b) (syn_ccnv (.cv f)))
      (syn_wa (syn_wf1o (.cv b) (.cv x) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (.cv x) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (.cv y)))
      (syn_wbr (syn_cpwpull (.cv b) (.cv a)) (syn_cwe) (.cv x))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (.cv x)) p0116 p0127
  have p0129 :=
    @g_pwpullwesetimpndv x y b a dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0130 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (.cv b) (.cv x) (.cv y)) (syn_wbr (.cv a) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (.cv b) (.cv a)) (syn_cwe) (.cv x)))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (.cv x) (.cv y))
          (syn_wbr (.cv a) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (.cv x)))
      b (syn_ccnv (.cv f)) dv_cache_0009 dv_cache_0010 p0112 p0128 p0129
  have p0131 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (.cv x) (.cv y))
          (syn_wbr (.cv a) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (.cv x)))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
          (syn_wbr (.cv a) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))))
      x (syn_crn (.cv f)) dv_cache_0011 dv_cache_0012 p0102 p0109 p0130
  have p0132 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
          (syn_wbr (.cv a) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
          (syn_wbr (.cv a) (syn_cwe) (syn_chnord A)))
        (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))))
      y (syn_chnord A) dv_cache_0013 dv_cache_0014 p0092 p0099 p0131
  have p0133 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
          (syn_wbr (.cv a) (syn_cwe) (syn_chnord A)))
        (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cwe) (syn_crn (.cv f))))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
          (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))
        (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv s)) (syn_cwe) (syn_crn (.cv f))))
      a (.cv s) dv_cache_0015 dv_cache_0016 p0076 p0091 p0132
  have p0134 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv s)) (syn_cwe) (syn_crn (.cv f))) p0075
      p0133
  have p0136 := @g_cnvcnv (.cv f)
  have p0137 := @g_coeq1i (syn_ccnv (syn_ccnv (.cv f))) (.cv f) (.cv s) p0136
  have p0138 :=
    @g_coeq1i (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv s)) (syn_ccom (.cv f) (.cv s))
      (syn_ccnv (.cv f)) p0137
  have p0139 :=
    @g_eqtri (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (.cv f))) (.cv s)) (syn_ccnv (.cv f)))
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) p0087 p0138
  have p0140 :=
    @g_breq1i (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f)) (syn_cwe)
      p0139
  have p0141 :=
    @g_sylib
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (syn_cpwpull (syn_ccnv (.cv f)) (.cv s)) (syn_cwe) (syn_crn (.cv f)))
      (syn_wbr (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_cwe)
        (syn_crn (.cv f)))
      p0134 p0140
  have p0142 := @g_f1f (syn_chnord A) (syn_cpw1 (syn_cpw1 A)) (.cv f)
  have p0143 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (syn_wf (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) p0000 p0142
  have p0144 := @g_frn (syn_chnord A) (syn_cpw1 (syn_cpw1 A)) (.cv f)
  have p0145 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (syn_wss (syn_crn (.cv f)) (syn_cpw1 (syn_cpw1 A))) p0143 p0144
  have p0146 :=
    @g_jca
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_cwe)
        (syn_crn (.cv f)))
      (syn_wss (syn_crn (.cv f)) (syn_cpw1 (syn_cpw1 A))) p0141 p0145
  have p0149 :=
    @g_pm3_2i (.classMem (.cv f) (syn_cvv)) (.classMem (.cv s) (syn_cvv)) p0100 p0076
  have p0150 := @g_coexg (.cv f) (.cv s) (syn_cvv) (syn_cvv)
  have p0151 := Nominal.mp p0149 p0150
  have p0155 :=
    @g_pm3_2i (.classMem (syn_ccom (.cv f) (.cv s)) (syn_cvv))
      (.classMem (syn_ccnv (.cv f)) (syn_cvv)) p0151 p0112
  have p0156 := @g_coexg (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)) (syn_cvv) (syn_cvv)
  have p0157 := Nominal.mp p0155 p0156
  have p0161 :=
    @g_elhwcodesclndv (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
      (syn_crn (.cv f)) (syn_cpw1 (syn_cpw1 A)) p0157 p0102
  have p0162 :=
    @g_sylibr
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (syn_wbr (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_cwe)
          (syn_crn (.cv f))) (syn_wss (syn_crn (.cv f)) (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chwcodes (syn_cpw1 (syn_cpw1 A))))
      p0146 p0161
  have p0163 := @g_f1ofo (syn_crn (.cv f)) (syn_chnord A) (syn_ccnv (.cv f))
  have p0164 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A)) p0004 p0163
  have p0166 := @g_biid (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
  have p0167 :=
    @g_a1i
      (syn_wb (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A)))
      (.classEq (.cv a) (.cv s)) p0166
  have p0176 :=
    @g_sseq1d (.classEq (.cv a) (.cv s)) (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
      (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
      (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))) p0089
  have p0177 :=
    @g_imbi12d (.classEq (.cv a) (.cv s))
      (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      p0167 p0176
  have p0179 := @g_foeq3 (.cv y) (syn_chnord A) (syn_crn (.cv f)) (syn_ccnv (.cv f))
  have p0180 :=
    @g_biid
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
  have p0181 :=
    @g_a1i
      (syn_wb (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
          (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
        (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
          (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))
      (.classEq (.cv y) (syn_chnord A)) p0180
  have p0182 :=
    @g_imbi12d (.classEq (.cv y) (syn_chnord A))
      (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
      (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      p0179 p0181
  have p0186 := @g_foeq2 (.cv x) (syn_crn (.cv f)) (.cv y) (syn_ccnv (.cv f))
  have p0189 :=
    @g_xpeq12d (.classEq (.cv x) (syn_crn (.cv f))) (.cv x) (syn_crn (.cv f)) (.cv x)
      (syn_crn (.cv f)) p0107 p0107
  have p0190 :=
    @g_sseq2d (.classEq (.cv x) (syn_crn (.cv f))) (syn_cxp (.cv x) (.cv x))
      (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))
      (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) p0189
  have p0191 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (.cv f)))
      (syn_wfo (syn_ccnv (.cv f)) (.cv x) (.cv y))
      (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cxp (.cv x) (.cv x)))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      p0186 p0190
  have p0195 := @g_foeq1 (.cv x) (.cv y) (.cv b) (syn_ccnv (.cv f))
  have p0206 :=
    @g_sseq1d (.classEq (.cv b) (syn_ccnv (.cv f))) (syn_cpwpull (.cv b) (.cv a))
      (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cxp (.cv x) (.cv x)) p0126
  have p0207 :=
    @g_imbi12d (.classEq (.cv b) (syn_ccnv (.cv f))) (syn_wfo (.cv b) (.cv x) (.cv y))
      (syn_wfo (syn_ccnv (.cv f)) (.cv x) (.cv y))
      (syn_wss (syn_cpwpull (.cv b) (.cv a)) (syn_cxp (.cv x) (.cv x)))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cxp (.cv x) (.cv x))) p0195
      p0206
  have p0208 :=
    @g_pwpullssxpsetimpndv x y b a dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0209 :=
    @g_vtocl
      (.imp (syn_wfo (.cv b) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (.cv b) (.cv a)) (syn_cxp (.cv x) (.cv x))))
      (.imp (syn_wfo (syn_ccnv (.cv f)) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cxp (.cv x) (.cv x))))
      b (syn_ccnv (.cv f)) dv_cache_0009 dv_cache_0017 p0112 p0207 p0208
  have p0210 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (.cv f)) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a)) (syn_cxp (.cv x) (.cv x))))
      (.imp (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
        (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
          (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))
      x (syn_crn (.cv f)) dv_cache_0011 dv_cache_0018 p0102 p0191 p0209
  have p0211 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (.cv y))
        (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
          (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))
      (.imp (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
          (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))
      y (syn_chnord A) dv_cache_0013 dv_cache_0019 p0092 p0182 p0210
  have p0212 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv a))
          (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))
      (.imp (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
        (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
          (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))))
      a (.cv s) dv_cache_0015 dv_cache_0020 p0076 p0177 p0211
  have p0213 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wfo (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_chnord A))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      p0164 p0212
  have p0219 :=
    @g_sseq1i (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
      (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))) p0139
  have p0220 :=
    @g_sylib
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wss (syn_cpwpull (syn_ccnv (.cv f)) (.cv s))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      (syn_wss (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      p0213 p0219
  have p0235 :=
    @g_opfv1st (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))
      p0157 p0102
  have p0236 :=
    @g_eqcomi
      (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))))
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) p0235
  have p0251 :=
    @g_opfv2nd (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))
      p0157 p0102
  have p0267 :=
    @g_xpeq12i
      (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))))
      (syn_crn (.cv f))
      (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))))
      (syn_crn (.cv f)) p0251 p0251
  have p0268 :=
    @g_eqcomi
      (syn_cxp (syn_cfv (syn_c2nd)
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f)))))
      (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))) p0267
  have p0269 :=
    @g_sseq12i (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
      (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))))
      (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f)))
      (syn_cxp (syn_cfv (syn_c2nd)
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f)))))
      p0236 p0268
  have p0270 :=
    @g_sylib
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wss (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_cxp (syn_crn (.cv f)) (syn_crn (.cv f))))
      (syn_wss (syn_cfv (syn_c1st)
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f)))) (syn_cfv (syn_c2nd)
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))))))
      p0220 p0269
  have p0271 :=
    @g_jca
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chwcodes (syn_cpw1 (syn_cpw1 A))))
      (syn_wss (syn_cfv (syn_c1st)
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f)))) (syn_cfv (syn_c2nd)
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))))))
      p0162 p0270
  have p0286 :=
    @g_pm3_2i
      (.classMem (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_cvv))
      (.classMem (syn_crn (.cv f)) (syn_cvv)) p0157 p0102
  have p0287 :=
    @g_opexg (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))
      (syn_cvv) (syn_cvv)
  have p0288 := Nominal.mp p0286 p0287
  have p0289 :=
    @g_elhwcncl (syn_cpw1 (syn_cpw1 A))
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
  have p0290 := Nominal.mp p0288 p0289
  have p0291 :=
    @g_sylibr
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chwcodes (syn_cpw1 (syn_cpw1 A)))) (syn_wss
          (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f)))) (syn_cxp (syn_cfv (syn_c2nd)
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f)))) (syn_cfv (syn_c2nd)
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f)))))))
      (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0271 p0290
  have p0292 := @g_f1odm (syn_chnord A) (syn_crn (.cv f)) (.cv f)
  have p0293 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (.cv f) (syn_chnord A) (syn_crn (.cv f)))
      (.classEq (syn_cdm (.cv f)) (syn_chnord A)) p0002 p0292
  have p0294 := @g_f1oeq2 (syn_cdm (.cv f)) (syn_chnord A) (syn_crn (.cv f)) (.cv f)
  have p0295 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classEq (syn_cdm (.cv f)) (syn_chnord A))
      (syn_wb (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wf1o (.cv f) (syn_chnord A) (syn_crn (.cv f))))
      p0293 p0294
  have p0296 :=
    @g_mpbird
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf1o (.cv f) (syn_chnord A) (syn_crn (.cv f))) p0002 p0295
  have p0297 :=
    @g_brco z (.cv x) (.cv y) (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)) dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0298 := @g_f1ocnv (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv f)
  have p0299 := @g_f1ofun (syn_crn (.cv f)) (syn_cdm (.cv f)) (syn_ccnv (.cv f))
  have p0300 :=
    @g_syl (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_cdm (.cv f)))
      (syn_wfun (syn_ccnv (.cv f))) p0298 p0299
  have p0301 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wfun (syn_ccnv (.cv f)))
      p0296 p0300
  have p0302 := @g_funbrfv2b (.cv x) (.cv z) (syn_ccnv (.cv f))
  have p0303 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wfun (syn_ccnv (.cv f)))
      (syn_wb (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))))
      p0301 p0302
  have p0304 :=
    @g_anbi1d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)) p0303
  have p0305 :=
    @g_exbidv
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      z dv_cache_0025 p0304
  have p0306 :=
    @g_anass (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))
  have p0307 :=
    @g_exbii
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      z p0306
  have p0308 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wex z (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))))
      p0305 p0307
  have p0309 :=
    @g_n_19_42v (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      z dv_cache_0026
  have p0310 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))))
      p0308 p0309
  have p0311 := @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)
  have p0312 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
      (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)) p0311
  have p0313 :=
    @g_exbii
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      z p0312
  have p0314 := @g_fvex (.cv x) (syn_ccnv (.cv f))
  have p0315 :=
    @g_breq1 (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y)
      (syn_ccom (.cv f) (.cv s))
  have p0316 :=
    @g_ceqsexv (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y)) z
      (syn_cfv (syn_ccnv (.cv f)) (.cv x)) dv_cache_0027 dv_cache_0028 p0314 p0315
  have p0317 :=
    @g_bitri
      (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y))
      p0313 p0316
  have p0318 :=
    @g_anbi2i
      (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y))
      (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0317
  have p0319 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y)))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      p0310 p0318
  have p0320 := @g_dfrn4 (.cv f)
  have p0321 := @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv x) p0320
  have p0322 :=
    @g_bicomi (.classMem (.cv x) (syn_crn (.cv f)))
      (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0321
  have p0323 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (.classMem (.cv x) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y))
      p0322
  have p0324 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      p0319 p0323
  have p0325 :=
    @g_syl5bb
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv s)) (.cv y))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      p0297 p0324
  have p0326 :=
    @g_brco w (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y) (.cv f) (.cv s) dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
  have p0327 := @g_brcnv (.cv y) (.cv w) (.cv f)
  have p0328 :=
    @g_bicomi (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))
      (syn_wbr (.cv w) (.cv f) (.cv y)) p0327
  have p0329 := @g_funbrfv2b (.cv y) (.cv w) (syn_ccnv (.cv f))
  have p0330 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wfun (syn_ccnv (.cv f)))
      (syn_wb (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      p0301 p0329
  have p0331 :=
    @g_syl5bb (syn_wbr (.cv w) (.cv f) (.cv y))
      (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
      p0328 p0330
  have p0332 :=
    @g_anbi2d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (.cv w) (.cv f) (.cv y))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)) p0331
  have p0333 :=
    @g_exbidv
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
        (syn_wbr (.cv w) (.cv f) (.cv y)))
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      w dv_cache_0033 p0332
  have p0334 :=
    @g_ancom (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
  have p0335 :=
    @g_anass (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
  have p0336 :=
    @g_bitri
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      p0334 p0335
  have p0337 :=
    @g_exbii
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      w p0336
  have p0338 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))))
      (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)))))
      p0333 p0337
  have p0339 :=
    @g_n_19_42v (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)))
      w dv_cache_0034
  have p0340 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)))))
      p0338 p0339
  have p0341 := @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)
  have p0342 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
      (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)) p0341
  have p0343 :=
    @g_exbii
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)))
      (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)))
      w p0342
  have p0344 := @g_fvex (.cv y) (syn_ccnv (.cv f))
  have p0345 :=
    @g_breq2 (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))
      (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
  have p0346 :=
    @g_ceqsexv (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      w (syn_cfv (syn_ccnv (.cv f)) (.cv y)) dv_cache_0035 dv_cache_0036 p0344 p0345
  have p0347 :=
    @g_bitri
      (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0343 p0346
  have p0348 :=
    @g_anbi2i
      (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0347
  have p0349 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w)))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0340 p0348
  have p0351 := @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv y) p0320
  have p0352 :=
    @g_bicomi (.classMem (.cv y) (syn_crn (.cv f)))
      (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0351
  have p0353 :=
    @g_anbi1i (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (.classMem (.cv y) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0352
  have p0354 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0349 p0353
  have p0355 :=
    @g_syl5bb
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0326 p0354
  have p0356 :=
    @g_anbi2d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (.classMem (.cv x) (syn_crn (.cv f))) p0355
  have p0357 :=
    @g_bitrd
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv s)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      p0325 p0356
  have p0358 :=
    @g_anass (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0359 :=
    @g_bicomi
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      p0358
  have p0360 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0357 p0359
  have p0361 := @g_vex x
  have p0362 := @g_vex y
  have p0363 := @g_simpl (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0364 :=
    @g_eleq1d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z)
      (.cv x) (syn_crn (.cv f)) p0363
  have p0365 := @g_simpr (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0366 :=
    @g_eleq1d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w)
      (.cv y) (syn_crn (.cv f)) p0365
  have p0367 :=
    @g_anbi12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv x) (syn_crn (.cv f)))
      (.classMem (.cv w) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))) p0364
      p0366
  have p0369 :=
    @g_fveq2d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z)
      (.cv x) (syn_ccnv (.cv f)) p0363
  have p0371 :=
    @g_fveq2d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w)
      (.cv y) (syn_ccnv (.cv f)) p0365
  have p0372 :=
    @g_breq12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (syn_cfv (syn_ccnv (.cv f)) (.cv x))
      (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv s)
      p0369 p0371
  have p0373 :=
    @g_anbi12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0367 p0372
  have p0374 :=
    @g_eqid
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
  have p0375 :=
    @g_braba
      (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
          (.classMem (.cv w) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      z w (.cv x) (.cv y)
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      dv_cache_0021 dv_cache_0037 dv_cache_0022 dv_cache_0030 dv_cache_0038 dv_cache_0039
      dv_cache_0040 p0361 p0362 p0373 p0374
  have p0376 :=
    @g_bicomi
      (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0375
  have p0377 :=
    @g_syl6bb
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))
      p0360 p0376
  have p0378 :=
    (Nominal.biimpRefl
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv y)))
  have p0379 :=
    (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab z w (syn_wa
            (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y)))
  have p0380 :=
    @g_n_3bitr3g
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab z w (syn_wa
            (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))))
      p0377 p0378 p0379
  have p0381 :=
    @g_eqrelrdv
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      x y (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
      dv_cache_0008 p0380
  have p0382 :=
    @g_a1d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_copab z w (syn_wa
            (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0381
  have p0383 := @g_f1ocnvdm (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv z) (.cv f)
  have p0384 :=
    @g_adantrr (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv z) (syn_crn (.cv f)))
      (.classMem (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (syn_cdm (.cv f)))
      (.classMem (.cv w) (syn_crn (.cv f))) p0383
  have p0385 :=
    @g_n_3adant3 (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
      (.classMem (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (syn_cdm (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      p0384
  have p0386 := @g_f1ocnvdm (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv w) (.cv f)
  have p0387 :=
    @g_adantrl (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv w) (syn_crn (.cv f)))
      (.classMem (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (syn_cdm (.cv f)))
      (.classMem (.cv z) (syn_crn (.cv f))) p0386
  have p0388 :=
    @g_n_3adant3 (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
      (.classMem (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (syn_cdm (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      p0387
  have p0389 := @g_f1ocnvfv2 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv z) (.cv f)
  have p0390 :=
    @g_eqcomd
      (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (.classMem (.cv z) (syn_crn (.cv f))))
      (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))) (.cv z) p0389
  have p0391 := @g_f1ocnvfv2 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv w) (.cv f)
  have p0392 :=
    @g_eqcomd
      (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (.classMem (.cv w) (syn_crn (.cv f))))
      (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w))) (.cv w) p0391
  have p0393 :=
    @g_anim12dan (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv z) (syn_crn (.cv f)))
      (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
      (.classMem (.cv w) (syn_crn (.cv f)))
      (.classEq (.cv w) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))) p0390
      p0392
  have p0394 :=
    @g_n_3adant3 (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
      (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      p0393
  have p0395 :=
    @g_simp3 (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
  have p0396 := @g_fveq2 (.cv b) (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (.cv f)
  have p0397 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      (syn_cfv (.cv f) (.cv b)) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      (.cv w) p0396
  have p0398 :=
    @g_anbi2d (.classEq (.cv b) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))
      (.classEq (.cv w) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z)))) p0397
  have p0399 :=
    @g_breq2 (.cv b) (syn_cfv (syn_ccnv (.cv f)) (.cv w))
      (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
  have p0400 :=
    @g_anbi12d (.classEq (.cv b) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
      (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s) (.cv b))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      p0398 p0399
  have p0401 :=
    @g_rspcev
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
          (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s) (.cv b)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
          (.classEq (.cv w) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      b (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (syn_cdm (.cv f)) dv_cache_0047 dv_cache_0048
      dv_cache_0049 p0400
  have p0402 :=
    @g_syl12anc
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      (.classMem (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (syn_cdm (.cv f)))
      (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      (syn_wrex b (syn_cdm (.cv f)) (syn_wa (syn_wa
            (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s) (.cv b))))
      p0388 p0394 p0395 p0401
  have p0403 := @g_fveq2 (.cv a) (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv f)
  have p0404 :=
    @g_eqeq2d (.classEq (.cv a) (syn_cfv (syn_ccnv (.cv f)) (.cv z)))
      (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z)))
      (.cv z) p0403
  have p0405 :=
    @g_anbi1d (.classEq (.cv a) (syn_cfv (syn_ccnv (.cv f)) (.cv z)))
      (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
      (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
      (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))) p0404
  have p0406 := @g_breq1 (.cv a) (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv b) (.cv s)
  have p0407 :=
    @g_anbi12d (.classEq (.cv a) (syn_cfv (syn_ccnv (.cv f)) (.cv z)))
      (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
        (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
      (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
        (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
      (syn_wbr (.cv a) (.cv s) (.cv b))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s) (.cv b)) p0405 p0406
  have p0408 :=
    @g_rexbidv (.classEq (.cv a) (syn_cfv (syn_ccnv (.cv f)) (.cv z)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
          (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
          (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s) (.cv b)))
      b (syn_cdm (.cv f)) dv_cache_0050 p0407
  have p0409 :=
    @g_rspcev
      (syn_wrex b (syn_cdm (.cv f)) (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (syn_wrex b (syn_cdm (.cv f)) (syn_wa (syn_wa
            (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s) (.cv b))))
      a (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (syn_cdm (.cv f)) dv_cache_0051 dv_cache_0052
      dv_cache_0053 p0408
  have p0410 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      (.classMem (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (syn_cdm (.cv f)))
      (syn_wrex b (syn_cdm (.cv f)) (syn_wa (syn_wa
            (.classEq (.cv z) (syn_cfv (.cv f) (syn_cfv (syn_ccnv (.cv f)) (.cv z))))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s) (.cv b))))
      (syn_wrex a (syn_cdm (.cv f)) (syn_wrex b (syn_cdm (.cv f)) (syn_wa
            (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
              (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))))
      p0385 p0402 p0409
  have p0411 :=
    @g_n_3expib (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      (syn_wrex a (syn_cdm (.cv f)) (syn_wrex b (syn_cdm (.cv f)) (syn_wa
            (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
              (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))))
      p0410
  have p0412 :=
    @g_simp3ll (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
      (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))) (syn_wbr (.cv a) (.cv s) (.cv b))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
  have p0413 :=
    @g_simp1 (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
          (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))
  have p0414 :=
    @g_simp2l (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
          (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))
  have p0415 := @g_f1of (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv f)
  have p0416 := @g_ffvelrn (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv a) (.cv f)
  have p0417 :=
    @g_sylan (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv a) (syn_cdm (.cv f)))
      (.classMem (syn_cfv (.cv f) (.cv a)) (syn_crn (.cv f))) p0415 p0416
  have p0418 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv a) (syn_cdm (.cv f)))
      (.classMem (syn_cfv (.cv f) (.cv a)) (syn_crn (.cv f))) p0413 p0414 p0417
  have p0419 :=
    @g_eqeltrd
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (.cv z) (syn_cfv (.cv f) (.cv a)) (syn_crn (.cv f)) p0412 p0418
  have p0420 :=
    @g_simp3lr (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
      (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))) (syn_wbr (.cv a) (.cv s) (.cv b))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
  have p0421 :=
    @g_simp2r (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
          (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))
  have p0422 := @g_ffvelrn (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv b) (.cv f)
  have p0423 :=
    @g_sylan (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv b) (syn_cdm (.cv f)))
      (.classMem (syn_cfv (.cv f) (.cv b)) (syn_crn (.cv f))) p0415 p0422
  have p0424 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv b) (syn_cdm (.cv f)))
      (.classMem (syn_cfv (.cv f) (.cv b)) (syn_crn (.cv f))) p0413 p0421 p0423
  have p0425 :=
    @g_eqeltrd
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (.cv w) (syn_cfv (.cv f) (.cv b)) (syn_crn (.cv f)) p0420 p0424
  have p0426 :=
    @g_simp3r (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
      (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
        (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
      (syn_wbr (.cv a) (.cv s) (.cv b))
  have p0427 :=
    @g_eqcomd
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (.cv z) (syn_cfv (.cv f) (.cv a)) p0412
  have p0428 := @g_f1ocnvfv (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv a) (.cv z) (.cv f)
  have p0429 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv a) (syn_cdm (.cv f)))
      (.imp (.classEq (syn_cfv (.cv f) (.cv a)) (.cv z))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv a)))
      p0413 p0414 p0428
  have p0430 :=
    @g_mpd
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (.classEq (syn_cfv (.cv f) (.cv a)) (.cv z))
      (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv a)) p0427 p0429
  have p0431 :=
    @g_eqcomd
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (.cv w) (syn_cfv (.cv f) (.cv b)) p0420
  have p0432 := @g_f1ocnvfv (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv b) (.cv w) (.cv f)
  have p0433 :=
    @g_syl2anc
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv b) (syn_cdm (.cv f)))
      (.imp (.classEq (syn_cfv (.cv f) (.cv b)) (.cv w))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (.cv b)))
      p0413 p0421 p0432
  have p0434 :=
    @g_mpd
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (.classEq (syn_cfv (.cv f) (.cv b)) (.cv w))
      (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (.cv b)) p0431 p0433
  have p0435 :=
    @g_n_3brtr4d
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (.cv a) (.cv b) (syn_cfv (syn_ccnv (.cv f)) (.cv z))
      (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (.cv s) p0426 p0430 p0434
  have p0436 :=
    @g_jca31
      (syn_w3a (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
        (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
            (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b))))
      (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      p0419 p0425 p0435
  have p0437 :=
    @g_n_3exp (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
          (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))
      (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
          (.classMem (.cv w) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      p0436
  have p0438 :=
    @g_rexlimdvv (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
          (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))
      (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
          (.classMem (.cv w) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      a b (syn_cdm (.cv f)) (syn_cdm (.cv f)) dv_cache_0048 dv_cache_0054 dv_cache_0055
      dv_cache_0056 dv_cache_0057 dv_cache_0058 p0437
  have p0439 :=
    @g_impbid (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
          (.classMem (.cv w) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      (syn_wrex a (syn_cdm (.cv f)) (syn_wrex b (syn_cdm (.cv f)) (syn_wa
            (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
              (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))))
      p0411 p0438
  have p0440 :=
    @g_opabbidv (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
          (.classMem (.cv w) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      (syn_wrex a (syn_cdm (.cv f)) (syn_wrex b (syn_cdm (.cv f)) (syn_wa
            (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
              (.classEq (.cv w) (syn_cfv (.cv f) (.cv b)))) (syn_wbr (.cv a) (.cv s) (.cv b)))))
      z w dv_cache_0059 dv_cache_0060 p0439
  have p0441 :=
    @g_eqeq2d (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      (syn_copab z w (syn_wrex a (syn_cdm (.cv f)) (syn_wrex b (syn_cdm (.cv f)) (syn_wa
              (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
                (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
              (syn_wbr (.cv a) (.cv s) (.cv b))))))
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) p0440
  have p0442 :=
    @g_mpbidi (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_copab z w (syn_wa
            (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv s)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_copab z w
          (syn_wrex a (syn_cdm (.cv f)) (syn_wrex b (syn_cdm (.cv f)) (syn_wa
                (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
                  (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
                (syn_wbr (.cv a) (.cv s) (.cv b)))))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      p0382 p0441
  have p0443 :=
    @g_f1oiso a b z w (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv s)
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv f) dv_cache_0061
      dv_cache_0052 dv_cache_0048 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0031
      dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0032 dv_cache_0015 dv_cache_0068
      dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0058 dv_cache_0073
      dv_cache_0074
  have p0444 :=
    @g_ex (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_copab z w
          (syn_wrex a (syn_cdm (.cv f)) (syn_wrex b (syn_cdm (.cv f)) (syn_wa
                (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
                  (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
                (syn_wbr (.cv a) (.cv s) (.cv b)))))))
      (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0443
  have p0445 :=
    @g_syl9
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_copab z w
          (syn_wrex a (syn_cdm (.cv f)) (syn_wrex b (syn_cdm (.cv f)) (syn_wa
                (syn_wa (.classEq (.cv z) (syn_cfv (.cv f) (.cv a)))
                  (.classEq (.cv w) (syn_cfv (.cv f) (.cv b))))
                (syn_wbr (.cv a) (.cv s) (.cv b)))))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0442 p0444
  have p0446 := @g_id (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
  have p0447 :=
    @g_a1ii
      (.imp (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
        (.imp (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
          (.imp (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv s)
              (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))))))
      (.imp (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))))
      p0445 p0446
  have p0448 :=
    @g_pm2_43d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0447
  have p0449 :=
    @g_mpd
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0296 p0448
  have p0450 :=
    @g_isoeq4 (syn_cdm (.cv f)) (syn_crn (.cv f)) (syn_chnord A) (.cv s)
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv f)
  have p0451 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classEq (syn_cdm (.cv f)) (syn_chnord A))
      (syn_wb (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_chnord A) (syn_crn (.cv f))))
      p0293 p0450
  have p0452 :=
    @g_mpbid
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_chnord A) (syn_crn (.cv f)))
      p0449 p0451
  have p0453 :=
    @g_isoeq2 (syn_chnord A) (syn_crn (.cv f)) (.cv s)
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
      (syn_clnqord (.cv r) (syn_chwcn A)) (.cv f)
  have p0454 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))
      (syn_wb (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_chnord A) (syn_crn (.cv f)))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
          (syn_crn (.cv f))))
      p0072 p0453
  have p0455 :=
    @g_mpbid
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wiso (.cv f) (.cv s) (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
        (syn_chnord A) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
        (syn_crn (.cv f)))
      p0452 p0454
  have p0456 :=
    @g_jca
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
        (syn_crn (.cv f)))
      p0291 p0455
  have p0471 :=
    @g_op1std (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))
      (.cv u) p0157 p0102
  have p0472 :=
    @g_isoeq3 (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))
      (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv f)
  have p0473 :=
    @g_syl
      (.classEq (.cv u) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))))
      (.classEq (syn_cfv (syn_c1st) (.cv u))
        (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))))
      (syn_wb (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
          (syn_cfv (syn_c2nd) (.cv u))))
      p0471 p0472
  have p0488 :=
    @g_op2ndd (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f))
      (.cv u) p0157 p0102
  have p0489 :=
    @g_isoeq5 (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv f))
      (syn_clnqord (.cv r) (syn_chwcn A))
      (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (.cv f)
  have p0490 :=
    @g_syl
      (.classEq (.cv u) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))))
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv f)))
      (syn_wb (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
          (syn_cfv (syn_c2nd) (.cv u))) (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
          (syn_crn (.cv f))))
      p0488 p0489
  have p0491 :=
    @g_bitrd
      (.classEq (.cv u) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
        (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
        (syn_crn (.cv f)))
      p0473 p0490
  have p0492 :=
    @g_rspcev
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
        (syn_crn (.cv f)))
      u
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      (syn_chwcn (syn_cpw1 (syn_cpw1 A))) dv_cache_0075 dv_cache_0076 dv_cache_0077 p0491
  have p0493 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_ccom (syn_ccom (.cv f) (.cv s)) (syn_ccnv (.cv f))) (syn_chnord A)
          (syn_crn (.cv f))))
      (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A)))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      p0456 p0492
  have p0494 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
  have p0495 :=
    @g_hncodepw12repdndv v u A dv_cache_0078 dv_cache_0079 dv_cache_0080
      hyp_hninjraisedselfcutalldndv_1
  have p0496 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0494 p0495
  have p0497 :=
    @g_nfv
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      v dv_cache_0081
  have p0498 :=
    @g_nfri
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      v p0497
  have p0499 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
  have p0501 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) p0499 p0494
  have p0502 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
  have p0503 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
  have p0504 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (.classMem (.cv v) (syn_chwcn A)) p0502 p0503
  have p0506 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
  have p0507 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      p0499 p0506
  have p0509 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
  have p0510 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      p0502 p0509
  have p0511 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      p0507 p0510
  have p0512 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0504 p0511
  have p0513 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      p0501 p0512
  have p0514 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
  have p0515 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
  have p0516 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (syn_wa (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0514 p0515
  have p0517 :=
    @g_simpl
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
  have p0518 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      p0516 p0517
  have p0519 :=
    @g_isof1o (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))
      (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u)) (.cv f)
  have p0520 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wf1o (.cv f) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))) p0518 p0519
  have p0521 := @g_f1of (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)) (.cv f)
  have p0522 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wf1o (.cv f) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wf (.cv f) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))) p0520 p0521
  have p0524 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
  have p0525 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (.classMem (.cv v) (syn_chwcn A)) p0514 p0524
  have p0526 := @g_hwnisoclasselhnordcl A (.cv v) hyp_hninjraisedselfcutalldndv_1
  have p0527 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cec (.cv v) (syn_chwniso A)) (syn_chnord A)) p0525 p0526
  have p0528 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wf (.cv f) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (syn_cec (.cv v) (syn_chwniso A)) (syn_chnord A)) p0522 p0527
  have p0529 :=
    @g_ffvelrn (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cec (.cv v) (syn_chwniso A)) (.cv f)
  have p0530 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wf (.cv f) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (syn_cec (.cv v) (syn_chwniso A)) (syn_chnord A)))
      (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_cfv (syn_c2nd) (.cv u)))
      p0528 p0529
  have p0534 :=
    @g_simpr
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
  have p0535 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      p0516 p0534
  have p0536 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
  have p0537 := @g_hnsicodemap2valclndv v A dv_cache_0079 hyp_hninjraisedselfcutalldndv_1
  have p0538 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
            (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (.classMem
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      p0525 p0537
  have p0539 :=
    @g_simpr
      (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
  have p0540 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
            (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (.classMem
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0538 p0539
  have p0541 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0536 p0540
  have p0542 := @g_pw1ex A hyp_hninjraisedselfcutalldndv_1
  have p0543 := @g_pw1ex (syn_cpw1 A) p0542
  have p0544 :=
    @g_hwnisoclasseqbcl (syn_cpw1 (syn_cpw1 A)) (.cv u)
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      p0543
  have p0545 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0541 p0544
  have p0546 :=
    @g_mpbird
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      p0535 p0545
  have p0550 := Nominal.mp hyp_hninjraisedselfcutalldndv_1 p0010
  have p0551 :=
    @g_syl6eqel
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.cv r) (syn_chncodecmpset A) (syn_cvv) p0007 p0550
  have p0552 := @g_hwcnex A hyp_hninjraisedselfcutalldndv_1
  have p0553 :=
    @g_jctir
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0551 p0552
  have p0554 := @g_lnqordexg (syn_chwcn A) (.cv r) dv_cache_0001
  have p0555 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv)) p0553 p0554
  have p0556 := @g_idex
  have p0557 :=
    @g_difexg (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid) (syn_cvv) (syn_cvv)
  have p0558 :=
    @g_sylancl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv))
      (.classMem (syn_cid) (syn_cvv))
      (.classMem (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cvv)) p0555
      p0556 p0557
  have p0559 :=
    @g_cnvexg (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cvv)
  have p0560 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cvv))
      (.classMem (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_cvv))
      p0558 p0559
  have p0561 := @g_snex (syn_cec (.cv v) (syn_chwniso A))
  have p0562 :=
    @g_imaexg (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
      (syn_csn (syn_cec (.cv v) (syn_chwniso A))) (syn_cvv) (syn_cvv)
  have p0563 :=
    @g_sylancl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_cvv))
      (.classMem (syn_csn (syn_cec (.cv v) (syn_chwniso A))) (syn_cvv))
      (.classMem (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv v) (syn_chwniso A)))) (syn_cvv))
      p0560 p0561 p0562
  have p0564 :=
    @g_inexg (syn_chnord A)
      (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
        (syn_csn (syn_cec (.cv v) (syn_chwniso A))))
      (syn_cvv) (syn_cvv)
  have p0565 :=
    @g_sylancr
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (syn_chnord A) (syn_cvv))
      (.classMem (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv v) (syn_chwniso A)))) (syn_cvv))
      (.classMem (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cvv))
      p0092 p0563 p0564
  have p0566 :=
    @g_resexg (.cv f)
      (syn_cin (syn_chnord A)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_cvv) (syn_cvv)
  have p0567 :=
    @g_sylancr
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (.cv f) (syn_cvv))
      (.classMem (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cvv))
      (.classMem (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_cvv))
      p0100 p0565 p0566
  have p0568 :=
    @g_a1d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      p0567
  have p0569 := @g_hnqmap1exg A
  have p0570 := Nominal.mp hyp_hninjraisedselfcutalldndv_1 p0569
  have p0571 :=
    (Nominal.classEqRefl
      (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0572 :=
    (Nominal.classEqRefl
      (syn_chnwcutfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0573 := (Nominal.classEqRefl (syn_chnwcodefn (syn_cfv (syn_c1st) (.cv v))))
  have p0575 := @g_hwcnweclndv A (.cv v)
  have p0576 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v))) p0525
      p0575
  have p0577 :=
    @g_brex (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cwe)
  have p0578 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv v)) (syn_cvv))
        (.classMem (syn_cfv (syn_c2nd) (.cv v)) (syn_cvv)))
      p0576 p0577
  have p0579 :=
    @g_simpld
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cfv (syn_c1st) (.cv v)) (syn_cvv))
      (.classMem (syn_cfv (syn_c2nd) (.cv v)) (syn_cvv)) p0578
  have p0580 := @g_resexg (syn_cid) (syn_cfv (syn_c1st) (.cv v)) (syn_cvv) (syn_cvv)
  have p0581 :=
    @g_sylancr
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cid) (syn_cvv)) (.classMem (syn_cfv (syn_c1st) (.cv v)) (syn_cvv))
      (.classMem (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))) (syn_cvv)) p0556 p0579
      p0580
  have p0582 := @g_imageexg (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))) (syn_cvv)
  have p0583 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))) (syn_cvv))
      (.classMem (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v)))) (syn_cvv))
      p0581 p0582
  have p0584 := @g_crossex
  have p0587 := @g_txpex (syn_cid) (syn_cid) p0556 p0556
  have p0588 := @g_coex (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)) p0584 p0587
  have p0589 :=
    @g_coexg (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) (syn_cvv) (syn_cvv)
  have p0590 :=
    @g_sylancl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v)))) (syn_cvv))
      (.classMem (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) (syn_cvv))
      (.classMem (syn_ccom (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cvv))
      p0583 p0588 p0589
  have p0592 :=
    @g_txpexg
      (syn_ccom (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))))
        (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))))
      (syn_cid) (syn_cvv) (syn_cvv)
  have p0593 :=
    @g_sylancl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_ccom (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cvv))
      (.classMem (syn_cid) (syn_cvv))
      (.classMem (syn_ctxp
          (syn_ccom (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))))
            (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_cvv))
      p0590 p0556 p0592
  have p0594 :=
    @g_syl5eqel
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_chnwcodefn (syn_cfv (syn_c1st) (.cv v)))
      (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c1st) (.cv v))))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))
      (syn_cvv) p0573 p0593
  have p0595 :=
    (Nominal.classEqRefl
      (syn_chnwsegfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0597 :=
    @g_simprd
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cfv (syn_c1st) (.cv v)) (syn_cvv))
      (.classMem (syn_cfv (syn_c2nd) (.cv v)) (syn_cvv)) p0578
  have p0598 := @g_resexg (syn_cid) (syn_cfv (syn_c2nd) (.cv v)) (syn_cvv) (syn_cvv)
  have p0599 :=
    @g_sylancr
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cid) (syn_cvv)) (.classMem (syn_cfv (syn_c2nd) (.cv v)) (syn_cvv))
      (.classMem (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv v))) (syn_cvv)) p0556 p0597
      p0598
  have p0600 := @g_imageexg (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv v))) (syn_cvv)
  have p0601 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv v))) (syn_cvv))
      (.classMem (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv))
      p0599 p0600
  have p0603 := @g_difexg (syn_cfv (syn_c1st) (.cv v)) (syn_cid) (syn_cvv) (syn_cvv)
  have p0604 :=
    @g_sylancl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cfv (syn_c1st) (.cv v)) (syn_cvv)) (.classMem (syn_cid) (syn_cvv))
      (.classMem (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cvv)) p0579 p0556
      p0603
  have p0605 := @g_cnvexg (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cvv)
  have p0606 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cvv))
      (.classMem (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_cvv))
      p0604 p0605
  have p0607 :=
    @g_imageexg (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_cvv)
  have p0608 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_cvv))
      (.classMem (syn_cimage (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))))
        (syn_cvv))
      p0606 p0607
  have p0609 :=
    @g_coexg (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cimage (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))) (syn_cvv)
      (syn_cvv)
  have p0610 :=
    @g_syl2anc
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv))
      (.classMem (syn_cimage (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))))
        (syn_cvv))
      (.classMem (syn_ccom (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cimage (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))))) (syn_cvv))
      p0601 p0608 p0609
  have p0611 :=
    @g_syl5eqel
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_chnwsegfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_ccom (syn_cimage (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv v))))
        (syn_cimage (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))))
      (syn_cvv) p0595 p0610
  have p0612 :=
    @g_coexg (syn_chnwcodefn (syn_cfv (syn_c1st) (.cv v)))
      (syn_chnwsegfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) (syn_cvv)
      (syn_cvv)
  have p0613 :=
    @g_syl2anc
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_chnwcodefn (syn_cfv (syn_c1st) (.cv v))) (syn_cvv))
      (.classMem (syn_chnwsegfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_cvv))
      (.classMem (syn_ccom (syn_chnwcodefn (syn_cfv (syn_c1st) (.cv v)))
          (syn_chnwsegfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv))
      p0594 p0611 p0612
  have p0614 :=
    @g_syl5eqel
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_chnwcutfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_ccom (syn_chnwcodefn (syn_cfv (syn_c1st) (.cv v)))
        (syn_chnwsegfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cvv) p0572 p0613
  have p0615 := @g_pw1exg (syn_cfv (syn_c2nd) (.cv v)) (syn_cvv)
  have p0616 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cfv (syn_c2nd) (.cv v)) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) (syn_cvv)) p0597 p0615
  have p0617 :=
    @g_resexg (syn_chnwcutfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) (syn_cvv) (syn_cvv)
  have p0618 :=
    @g_syl2anc
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_chnwcutfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_cvv))
      (.classMem (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) (syn_cvv))
      (.classMem (syn_cres
          (syn_chnwcutfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv))
      p0614 p0616 p0617
  have p0619 :=
    @g_syl5eqel
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_cres (syn_chnwcutfn (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cvv) p0571 p0618
  have p0620 :=
    @g_siexg (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_cvv)
  have p0621 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_cvv))
      (.classMem (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv))
      p0619 p0620
  have p0622 :=
    @g_coexg (syn_chnqmap1 A)
      (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cvv) (syn_cvv)
  have p0623 :=
    @g_sylancr
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_chnqmap1 A) (syn_cvv))
      (.classMem (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv))
      (.classMem (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_cvv))
      p0570 p0621 p0622
  have p0624 :=
    @g_coexg
      (syn_cres (.cv f) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_cvv) (syn_cvv)
  have p0625 :=
    @g_ex
      (.classMem (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_cvv))
      (.classMem (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_cvv))
      (.classMem (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cvv))
      p0624
  have p0626 :=
    @g_syl5
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_cvv))
      (.classMem (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_cvv))
      (.classMem (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cvv))
      p0623 p0625
  have p0627 :=
    @g_syl6
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_cvv))
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
              (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
                (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
              (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) (.classMem
          (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cvv)))
      p0568 p0626
  have p0628 :=
    @g_pm2_43d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cvv))
      p0627
  have p0629 :=
    @g_isset k
      (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))))
      dv_cache_0082
  have p0630 :=
    @g_syl6ib
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cvv))
      (syn_wex k (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v))))))))
      p0628 p0629
  have p0631 :=
    Nominal.ax17
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      k dv_cache_0083
  have p0638 :=
    @g_hnwcutambstrictsegresisomraliasdndv v A r dv_cache_0002 dv_cache_0079 dv_cache_0084
      hyp_hninjraisedselfcutalldndv_1
  have p0639 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
          (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
      p0007 p0638
  have p0640 :=
    @g_syl5
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
      p0525 p0639
  have p0641 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (syn_cec (.cv v) (syn_chwniso A)) (syn_chnord A)) p0518 p0527
  have p0642 :=
    @g_isostrictsegresclndv (syn_cec (.cv v) (syn_chwniso A)) (syn_chnord A)
      (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c2nd) (.cv u)) (.cv f)
  have p0643 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (syn_cec (.cv v) (syn_chwniso A)) (syn_chnord A)))
      (syn_wiso (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
        (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      p0641 p0642
  have p0644 :=
    @g_pm3_2
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_wiso (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
        (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
  have p0645 :=
    @g_syl5
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
        (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_wa (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
          (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_wiso (syn_cres (.cv f)
            (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
          (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0643 p0644
  have p0646 :=
    @g_syl6
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
              (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
                (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
              (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) (syn_wa
          (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
            (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
            (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
            (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_wiso (syn_cres (.cv f)
              (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
            (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
                (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                  (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                    (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
            (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))))
      p0640 p0645
  have p0647 :=
    @g_pm2_43d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
          (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_wiso (syn_cres (.cv f)
            (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
          (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0646
  have p0648 :=
    @g_isotr (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cin (syn_chnord A)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
      (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      (syn_cres (.cv f) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
  have p0649 :=
    @g_syl6
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
          (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_wiso (syn_cres (.cv f)
            (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A))))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
          (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v))))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cin (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      p0647 p0648
  have p0650 :=
    @g_simpl
      (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
  have p0651 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
            (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (.classMem
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))))
      p0538 p0650
  have p0652 := @g_fvex (.cv v) (syn_c1st)
  have p0653 := @g_siex (syn_cfv (syn_c1st) (.cv v)) p0652
  have p0654 := @g_siex (syn_csi (syn_cfv (syn_c1st) (.cv v))) p0653
  have p0655 := @g_fvex (.cv v) (syn_c2nd)
  have p0656 := @g_pw1ex (syn_cfv (syn_c2nd) (.cv v)) p0655
  have p0657 := @g_pw1ex (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0656
  have p0658 :=
    @g_op1std (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      p0654 p0657
  have p0659 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))))
      (.classEq (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))))
      p0651 p0658
  have p0660 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) p0659
  have p0661 :=
    @g_isoeq2 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))))
  have p0662 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (syn_wb (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v))))))
          (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cin (syn_cfv (syn_c1st) (.cv u))
            (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))) (syn_wiso
          (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0660 p0661
  have p0663 :=
    @g_mpbidi
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v))))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cin (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      p0649 p0662
  have p0664 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_cfv (syn_c2nd) (.cv u)))
      p0536 p0530
  have p0665 :=
    @g_hnwcutcodepartsclndv u (syn_cpw1 (syn_cpw1 A))
      (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))) dv_cache_0085
  have p0666 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
          (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))) (.classEq
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0664 p0665
  have p0667 :=
    @g_simpl
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
  have p0668 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))) (.classEq
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))))
      p0666 p0667
  have p0669 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0668
  have p0670 :=
    @g_isoeq3 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))))
  have p0671 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
        (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_wb (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))) (syn_wiso
          (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0669 p0670
  have p0672 :=
    @g_mpbidi
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      p0663 p0671
  have p0679 :=
    @g_op2ndd (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      p0654 p0657
  have p0680 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0651 p0679
  have p0681 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0680
  have p0682 :=
    @g_isoeq4 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))))
  have p0683 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (syn_wb (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))) (syn_wiso
          (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0681 p0682
  have p0684 :=
    @g_mpbidi
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      p0672 p0683
  have p0685 :=
    @g_simpr
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
  have p0686 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))) (.classEq
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      p0666 p0685
  have p0687 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      p0686
  have p0688 :=
    @g_isoeq5
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))))
  have p0689 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_wb (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))) (syn_wiso
          (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      p0687 p0688
  have p0690 :=
    @g_mpbidi
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      p0684 p0689
  have p0691 :=
    @g_a1dd
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))))
      p0690
  have p0692 :=
    @g_isoeq1
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))))
      (.cv k)
  have p0693 :=
    @g_biimprd
      (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))))
      (syn_wiso (.cv k) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      p0692
  have p0694 :=
    @g_a2i
      (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))))
      (syn_wiso (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_wiso (.cv k) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      p0693
  have p0695 :=
    @g_syl6
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.imp (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v))))))) (syn_wiso (syn_ccom (syn_cres (.cv f)
              (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (.imp (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v))))))) (syn_wiso (.cv k) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      p0691 p0694
  have p0696 :=
    @g_alimdv
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.imp (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v))))))) (syn_wiso (.cv k) (syn_cfv (syn_c1st)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      k dv_cache_0086 p0695
  have p0697 :=
    @g_syl5
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.all k (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
              (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
                (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
              (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.all k (.imp (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
                (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v))))))) (syn_wiso (.cv k) (syn_cfv (syn_c1st)
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0631 p0696
  have p0698 :=
    @g_exim
      (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv v)))))))
      (syn_wiso (.cv k) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      k
  have p0699 :=
    @g_syl6
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.all k (.imp (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
                (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v))))))) (syn_wiso (.cv k) (syn_cfv (syn_c1st)
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      (.imp (syn_wex k (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
                (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)))))))) (syn_wex k (syn_wiso (.cv k)
            (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0697 p0698
  have p0700 :=
    @g_mpdd
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wex k (.classEq (.cv k) (syn_ccom (syn_cres (.cv f) (syn_cin (syn_chnord A) (syn_cima
                  (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv v) (syn_chwniso A)))))) (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv v))
                  (syn_cfv (syn_c2nd) (.cv v))))))))
      (syn_wex k (syn_wiso (.cv k) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      p0630 p0699
  have p0701 :=
    @g_hnwcutcodeambientclndv u (syn_cpw1 (syn_cpw1 A))
      (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))) dv_cache_0085
  have p0702 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
          (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0664 p0701
  have p0703 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0540 p0702
  have p0704 :=
    @g_hwnisodirectisobclndv (syn_cpw1 (syn_cpw1 A))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
      k dv_cache_0087 dv_cache_0088 dv_cache_0089
  have p0705 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      (syn_wb (syn_wbr (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wex k (syn_wiso (.cv k)
            (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))))
      p0703 p0704
  have p0706 :=
    @g_biimprd
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wbr (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wex k (syn_wiso (.cv k) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      p0705
  have p0707 :=
    @g_sylcom
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wex k (syn_wiso (.cv k) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))) (syn_cfv (syn_c2nd)
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      (syn_wbr (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      p0700 p0706
  have p0710 :=
    @g_hwnisoclasseqbcl (syn_cpw1 (syn_cpw1 A))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
      p0543
  have p0711 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      (syn_wb (.classEq (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A))))) (syn_wbr
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      p0703 p0710
  have p0712 :=
    @g_biimprd
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      (syn_wbr (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      p0711
  have p0713 :=
    @g_sylcom
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wbr (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classEq (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      p0707 p0712
  have p0714 :=
    @g_eqeq2
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
      (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
  have p0715 :=
    @g_syl6
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A))))))
      p0713 p0714
  have p0716 :=
    @g_bi1
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
  have p0717 :=
    @g_syl6
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A))))))
      (.imp (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A))))))
      p0715 p0716
  have p0718 :=
    @g_mpdi
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      p0546 p0717
  have p0719 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0536 p0702
  have p0722 :=
    @g_hwnisoclasseqbcl (syn_cpw1 (syn_cpw1 A)) (.cv u)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
      p0543
  have p0723 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      p0719 p0722
  have p0724 :=
    @g_mpbidi
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      p0718 p0723
  have p0725 :=
    @g_pm3_2
      (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
  have p0726 :=
    @g_syl9
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wa (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
          (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      p0724 p0725
  have p0727 :=
    @g_syl5
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
              (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
                (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
              (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) (syn_wa
          (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
            (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))))
      p0530 p0726
  have p0728 :=
    @g_pm2_43d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
          (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      p0727
  have p0729 :=
    @g_hnwcutcodeeq3 (.cv x) (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0090
  have p0730 :=
    @g_breq2d (.classEq (.cv x) (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))
      (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) p0729
  have p0731 :=
    @g_rspcev
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))))
      x (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))) (syn_cfv (syn_c2nd) (.cv u))
      dv_cache_0091 dv_cache_0092 dv_cache_0093 p0730
  have p0732 :=
    @g_syl6
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (.classMem (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A)))
          (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cfv (.cv f) (syn_cec (.cv v) (syn_chwniso A))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0728 p0731
  have p0733 :=
    @g_syl5
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa
            (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0513 p0732
  have p0734 :=
    @g_exp4d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0733
  have p0735 :=
    @g_alimdv
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (.imp (.classMem (.cv v) (syn_chwcn A)) (.imp
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))))))
      v dv_cache_0094 p0734
  have p0736 :=
    @g_syl5
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (.all v (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
          (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cfv (syn_c1st) (.cv u)) (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.all v (.imp (.classMem (.cv v) (syn_chwcn A)) (.imp
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
            (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
              (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x)))))))
      p0498 p0735
  have p0737 :=
    (Nominal.biimpRefl (syn_wral v (syn_chwcn A) (.imp
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)))))))
  have p0738 :=
    @g_syl6ibr
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (.all v (.imp (.classMem (.cv v) (syn_chwcn A)) (.imp
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
            (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
              (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x)))))))
      (syn_wral v (syn_chwcn A) (.imp (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))))))
      p0736 p0737
  have p0739 :=
    @g_nfv
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      v dv_cache_0095
  have p0740 :=
    @g_r19_23
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      v (syn_chwcn A) p0739
  have p0741 :=
    @g_syl6ib
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wral v (syn_chwcn A) (.imp (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))))))
      (.imp (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      p0738 p0740
  have p0742 :=
    @g_mpdi
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0496 p0741
  have p0743 :=
    @g_exp3a
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0742
  have p0744 :=
    @g_reximdvai
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
        (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) dv_cache_0096 p0743
  have p0745 :=
    @g_mpd
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A)))
        (syn_wiso (.cv f) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
          (syn_chnord A) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      p0493 p0744
  exact p0745


end NFChoice.DirectNominalPrf.WPPReplay
