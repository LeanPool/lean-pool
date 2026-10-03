/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block021

/-! NF weak partition development: NominalWPPReplayChunk017Compact001Part090. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbfdwppcarrierimpndv (A : Class) (R : Class) (k : Var) (X : Class)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_X : Disjoint A.fv X.fv) (dv_A_k : k ∉ A.fv)
    (dv_R_X : Disjoint R.fv X.fv) (_dv_R_k : k ∉ R.fv) (dv_X_k : k ∉ X.fv)
    (hyp_cfbfdwppcarrierimpndv_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_cfbfdwppcarrierimpndv_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_cfbfdwppcarrierimpndv_3 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbfdwppcarrierimpndv_4 : Nominal.NPrf
        (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
          (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k
            (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 A)))
              (syn_cpw (syn_cpw (syn_chnord X))))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ R.fv ∪ ({ k } : Finset Var) ∪ X.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let f : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  let e : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  let c : Var := freshVar proofSupport 7
  let a : Var := freshVar proofSupport 8
  let b : Var := freshVar proofSupport 9
  let r : Var := freshVar proofSupport 10
  let p : Var := freshVar proofSupport 11
  let g : Var := freshVar proofSupport 12
  let h : Var := freshVar proofSupport 13
  let i : Var := freshVar proofSupport 14
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_X : f ∉ X.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_X : q ∉ X.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_e_not_A : e ∉ A.fv := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_e_not_R : e ∉ R.fv := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_e_not_X : e ∉ X.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_X : d ∉ X.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_X : c ∉ X.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 9 ∉ proofSupport
    exact freshVar_not_mem proofSupport 9
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_X : b ∉ X.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 10 ∉ proofSupport
    exact freshVar_not_mem proofSupport 10
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 11 ∉ proofSupport
    exact freshVar_not_mem proofSupport 11
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_X : p ∉ X.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 12 ∉ proofSupport
    exact freshVar_not_mem proofSupport 12
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_g_not_R : g ∉ R.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_X : g ∉ X.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 13 ∉ proofSupport
    exact freshVar_not_mem proofSupport 13
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_X : h ∉ X.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_i : i ∉ proofSupport :=
    by
    change freshVar proofSupport 14 ∉ proofSupport
    exact freshVar_not_mem proofSupport 14
  have fresh_i_not_A : i ∉ A.fv := by
    intro h
    exact
      fresh_i
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_i_not_R : i ∉ R.fv := by
    intro h
    exact
      fresh_i
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_i_not_X : i ∉ X.fv := by
    intro h
    exact fresh_i (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_q : y ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_e : y ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_e_ne_y : e ≠ y := Ne.symm fresh_y_ne_e
  have fresh_y_ne_d : y ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_y : d ≠ y := Ne.symm fresh_y_ne_d
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_e : x ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_e_ne_x : e ≠ x := Ne.symm fresh_x_ne_e
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_f_ne_q : f ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_f : q ≠ f := Ne.symm fresh_f_ne_q
  have fresh_f_ne_a : f ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_a_ne_f : a ≠ f := Ne.symm fresh_f_ne_a
  have fresh_f_ne_b : f ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_b_ne_f : b ≠ f := Ne.symm fresh_f_ne_b
  have fresh_f_ne_p : f ≠ p :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 3) (j := 11) (by decide)
  have fresh_p_ne_f : p ≠ f := Ne.symm fresh_f_ne_p
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 12
    exact freshVar_injective proofSupport (i := 3) (j := 12) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have fresh_f_ne_h : f ≠ h :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 13
    exact freshVar_injective proofSupport (i := 3) (j := 13) (by decide)
  have fresh_h_ne_f : h ≠ f := Ne.symm fresh_f_ne_h
  have fresh_f_ne_i : f ≠ i :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 14
    exact freshVar_injective proofSupport (i := 3) (j := 14) (by decide)
  have fresh_i_ne_f : i ≠ f := Ne.symm fresh_f_ne_i
  have fresh_q_ne_e : q ≠ e :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_e_ne_q : e ≠ q := Ne.symm fresh_q_ne_e
  have fresh_q_ne_a : q ≠ a :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_a_ne_q : a ≠ q := Ne.symm fresh_q_ne_a
  have fresh_q_ne_p : q ≠ p :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 4) (j := 11) (by decide)
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have fresh_q_ne_g : q ≠ g :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 12
    exact freshVar_injective proofSupport (i := 4) (j := 12) (by decide)
  have fresh_g_ne_q : g ≠ q := Ne.symm fresh_q_ne_g
  have fresh_q_ne_h : q ≠ h :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 13
    exact freshVar_injective proofSupport (i := 4) (j := 13) (by decide)
  have fresh_h_ne_q : h ≠ q := Ne.symm fresh_q_ne_h
  have fresh_q_ne_i : q ≠ i :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 14
    exact freshVar_injective proofSupport (i := 4) (j := 14) (by decide)
  have fresh_i_ne_q : i ≠ q := Ne.symm fresh_q_ne_i
  have fresh_e_ne_d : e ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_d_ne_e : d ≠ e := Ne.symm fresh_e_ne_d
  have fresh_e_ne_c : e ≠ c :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_c_ne_e : c ≠ e := Ne.symm fresh_e_ne_c
  have fresh_e_ne_a : e ≠ a :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_a_ne_e : a ≠ e := Ne.symm fresh_e_ne_a
  have fresh_e_ne_b : e ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
  have fresh_b_ne_e : b ≠ e := Ne.symm fresh_e_ne_b
  have fresh_d_ne_c : d ≠ c :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_c_ne_d : c ≠ d := Ne.symm fresh_d_ne_c
  have fresh_d_ne_b : d ≠ b :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_b_ne_d : b ≠ d := Ne.symm fresh_d_ne_b
  have fresh_c_ne_a : c ≠ a :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_a_ne_c : a ≠ c := Ne.symm fresh_c_ne_a
  have fresh_c_ne_b : c ≠ b :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 7) (j := 9) (by decide)
  have fresh_b_ne_c : b ≠ c := Ne.symm fresh_c_ne_b
  have fresh_c_ne_r : c ≠ r :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 7) (j := 10) (by decide)
  have fresh_r_ne_c : r ≠ c := Ne.symm fresh_c_ne_r
  have fresh_c_ne_h : c ≠ h :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 13
    exact freshVar_injective proofSupport (i := 7) (j := 13) (by decide)
  have fresh_h_ne_c : h ≠ c := Ne.symm fresh_c_ne_h
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 8) (j := 10) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have fresh_a_ne_p : a ≠ p :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 8) (j := 11) (by decide)
  have fresh_a_ne_g : a ≠ g :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 12
    exact freshVar_injective proofSupport (i := 8) (j := 12) (by decide)
  have fresh_a_ne_h : a ≠ h :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 13
    exact freshVar_injective proofSupport (i := 8) (j := 13) (by decide)
  have fresh_h_ne_a : h ≠ a := Ne.symm fresh_a_ne_h
  have fresh_a_ne_i : a ≠ i :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 14
    exact freshVar_injective proofSupport (i := 8) (j := 14) (by decide)
  have fresh_i_ne_a : i ≠ a := Ne.symm fresh_a_ne_i
  have fresh_b_ne_r : b ≠ r :=
    by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
  have fresh_r_ne_b : r ≠ b := Ne.symm fresh_b_ne_r
  have fresh_b_ne_h : b ≠ h :=
    by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 13
    exact freshVar_injective proofSupport (i := 9) (j := 13) (by decide)
  have fresh_h_ne_b : h ≠ b := Ne.symm fresh_b_ne_h
  have fresh_p_ne_g : p ≠ g :=
    by
    change freshVar proofSupport 11 ≠ freshVar proofSupport 12
    exact freshVar_injective proofSupport (i := 11) (j := 12) (by decide)
  have fresh_g_ne_p : g ≠ p := Ne.symm fresh_p_ne_g
  have fresh_p_ne_h : p ≠ h :=
    by
    change freshVar proofSupport 11 ≠ freshVar proofSupport 13
    exact freshVar_injective proofSupport (i := 11) (j := 13) (by decide)
  have fresh_h_ne_p : h ≠ p := Ne.symm fresh_p_ne_h
  have fresh_p_ne_i : p ≠ i :=
    by
    change freshVar proofSupport 11 ≠ freshVar proofSupport 14
    exact freshVar_injective proofSupport (i := 11) (j := 14) (by decide)
  have fresh_i_ne_p : i ≠ p := Ne.symm fresh_p_ne_i
  have fresh_g_ne_h : g ≠ h :=
    by
    change freshVar proofSupport 12 ≠ freshVar proofSupport 13
    exact freshVar_injective proofSupport (i := 12) (j := 13) (by decide)
  have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
  have fresh_g_ne_i : g ≠ i :=
    by
    change freshVar proofSupport 12 ≠ freshVar proofSupport 14
    exact freshVar_injective proofSupport (i := 12) (j := 14) (by decide)
  have fresh_i_ne_g : i ≠ g := Ne.symm fresh_g_ne_i
  have fresh_h_ne_i : h ≠ i :=
    by
    change freshVar proofSupport 13 ≠ freshVar proofSupport 14
    exact freshVar_injective proofSupport (i := 13) (j := 14) (by decide)
  have fresh_i_ne_h : i ≠ h := Ne.symm fresh_h_ne_i
  have dv_cache_0001 : Disjoint (A).fv (X).fv := by
    exact
      (show Disjoint (A).fv (X).fv from (show Disjoint (A).fv (X).fv from (by exact dv_A_X)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (X).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (X).fv (R).fv from
        (show Disjoint (X).fv (R).fv from (by exact dv_R_X.symm)))
  have dv_cache_0004 : x ∉ ((syn_cpw1fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cpw1fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_X, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_X, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_cpw (syn_cfdif R A X))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_X, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_cpw (syn_cpw (syn_cfdif R A X)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_X, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_wbr (.cv y) (syn_cpw1fn) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_cpw (syn_cpw (syn_cfdif R A X)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_X, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0015 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0016 : y ∉ ((syn_csn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_z,
          not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_X, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((syn_cpw1 (syn_cpw (syn_cfdif R A X)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_X, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((syn_cpw1 (syn_cpw (syn_cfdif R A X)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_X, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ ((syn_cfdif R A X)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_X, fresh_z_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0022 : y ∉ ((syn_cpw (syn_cfdif R A X))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_X, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_cpw (syn_cpw1 (syn_cfdif R A X)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_X, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0024 : e ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_q, not_false_eq_true])
  have dv_cache_0025 : e ∉ ((syn_cfdif R A X)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          Finset.mem_union, fresh_e_not_A, fresh_e_not_X, fresh_e_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0026 : e ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_e_ne_q, fresh_e_not_A, fresh_e_not_X, fresh_e_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0027 : e ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_A, not_false_eq_true])
  have dv_cache_0028 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0029 : y ∉ (A).fv :=
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0030 : e ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_X, not_false_eq_true])
  have dv_cache_0031 : x ∉ (X).fv :=
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
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0032 : y ∉ (X).fv :=
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
        simp only [fresh_y_not_X, not_false_eq_true])
  have dv_cache_0033 : e ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_R, not_false_eq_true])
  have dv_cache_0034 : x ∉ (R).fv :=
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
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0035 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0036 : e ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show e ≠ x from (by exact fresh_e_ne_x))
  have dv_cache_0037 : e ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact (show e ≠ y from (by exact fresh_e_ne_y))
  have dv_cache_0038 :
    x ∉
      ((syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))
            (.classMem (.cv e) (syn_cfdif R A X))) (.classEq (.cv q) (syn_csn (.cv e))))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_A, fresh_x_not_X, fresh_x_not_R,
          fresh_x_ne_e, or_false, not_false_eq_true])
  have dv_cache_0039 :
    y ∉
      ((syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))
              (.classMem (.cv e) (syn_cfdif R A X))) (.classEq (.cv q) (syn_csn (.cv e))))
          (.classMem (.cv x) X))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, fresh_y_not_A, fresh_y_not_X, fresh_y_not_R,
          fresh_y_ne_e, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0040 : Disjoint (A).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0041 : Disjoint (A).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (show Disjoint (A).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (A).fv from (by exact fresh_y_not_A))))))
  have dv_cache_0042 : Disjoint (X).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (show Disjoint (X).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((X).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (X).fv from (by exact fresh_x_not_X))))))
  have dv_cache_0043 : Disjoint (X).fv ((Class.cv y)).fv :=
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
      (show Disjoint (X).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((X).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (X).fv from (by exact fresh_y_not_X))))))
  have dv_cache_0044 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv :=
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
      (show Disjoint ((Class.cv x)).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (y)];
          exact
            (show Disjoint (({ x } : Finset Var)) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ ({ y } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show x ≠ y from (by exact fresh_x_ne_y))))))))
  have dv_cache_0045 : Disjoint ((Class.cv x)).fv (R).fv :=
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
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0046 : Disjoint ((Class.cv y)).fv (R).fv :=
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
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0047 : d ∉ ((Class.cv e)).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_e, not_false_eq_true])
  have dv_cache_0048 : c ∉ (A).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0049 : c ∉ ((Class.cv x)).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0050 : e ∉ ((Class.cv x)).fv :=
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
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_x, not_false_eq_true])
  have dv_cache_0051 : c ∉ ((Class.cv y)).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0052 : e ∉ ((Class.cv y)).fv :=
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
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_y, not_false_eq_true])
  have dv_cache_0053 : c ∉ (R).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_R, not_false_eq_true])
  have dv_cache_0054 : c ≠ e :=
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
    exact (show c ≠ e from (by exact fresh_c_ne_e))
  have dv_cache_0055 : d ∉ (A).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0056 : d ∉ ((Class.cv x)).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_x, not_false_eq_true])
  have dv_cache_0057 : d ∉ ((Class.cv y)).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_y, not_false_eq_true])
  have dv_cache_0058 : d ∉ (R).fv :=
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
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0059 : c ≠ d :=
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
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0060 : c ∉ ((Class.cv e)).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_e, not_false_eq_true])
  have dv_cache_0061 :
    c ∉
      ((Wff.imp (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y)))
          (syn_wbr (.cv d) R (.cv e)))).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_e, fresh_c_ne_x, fresh_c_ne_y, fresh_c_ne_d,
          fresh_c_not_R, or_false, not_false_eq_true])
  have dv_cache_0062 : c ∉ ((Class.cv d)).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_d, not_false_eq_true])
  have dv_cache_0063 :
    c ∉
      ((Wff.imp (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
          (syn_wbr (.cv e) R (.cv d)))).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_d, fresh_c_ne_x, fresh_c_ne_y, fresh_c_ne_e,
          fresh_c_not_R, or_false, not_false_eq_true])
  have dv_cache_0064 : a ∉ ((Wff.classEq (.cv r) R)).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_r, fresh_a_not_R, or_false, not_false_eq_true])
  have dv_cache_0065 : b ∉ ((Wff.classEq (.cv r) R)).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_r, fresh_b_not_R, or_false, not_false_eq_true])
  have dv_cache_0066 : b ∉ ((Class.cv c)).fv :=
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
          fresh_b_ne_c, not_false_eq_true])
  have dv_cache_0067 : b ∉ (A).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0068 : a ∉ ((Class.cv c)).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_c, not_false_eq_true])
  have dv_cache_0069 : a ∉ (A).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0070 : c ≠ r :=
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
    exact (show c ≠ r from (by exact fresh_c_ne_r))
  have dv_cache_0071 : c ≠ a :=
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
    exact (show c ≠ a from (by exact fresh_c_ne_a))
  have dv_cache_0072 : c ≠ b :=
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
    exact (show c ≠ b from (by exact fresh_c_ne_b))
  have dv_cache_0073 : r ≠ a :=
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
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0074 : r ≠ b :=
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
    exact (show r ≠ b from (by exact fresh_r_ne_b))
  have dv_cache_0075 : a ≠ b :=
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
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0076 : r ∉ (R).fv :=
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
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0077 : r ∉ (A).fv :=
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
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0078 :
    r ∉
      ((syn_wral a A (syn_wral b A
            (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a)))
              (.objEq a b))))).fv :=
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
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_a,
          fresh_r_ne_b, fresh_r_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0079 :
    c ∉
      ((syn_wral a A (syn_wral b A
            (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a)))
              (.objEq a b))))).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, fresh_c_ne_a,
          fresh_c_ne_b, fresh_c_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0080 : r ≠ c :=
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
    exact (show r ≠ c from (by exact fresh_r_ne_c))
  have dv_cache_0081 : a ∉ ((Class.cv e)).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_e, not_false_eq_true])
  have dv_cache_0082 : b ∉ ((Class.cv e)).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_e, not_false_eq_true])
  have dv_cache_0083 : b ∉ ((Class.cv d)).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_d, not_false_eq_true])
  have dv_cache_0084 :
    a ∉
      ((Wff.imp (syn_wa (syn_wbr (.cv e) R (.cv b)) (syn_wbr (.cv b) R (.cv e)))
          (.classEq (.cv e) (.cv b)))).fv :=
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
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_e, fresh_a_ne_b, fresh_a_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0085 :
    b ∉
      ((Wff.imp (syn_wa (syn_wbr (.cv e) R (.cv d)) (syn_wbr (.cv d) R (.cv e)))
          (.classEq (.cv e) (.cv d)))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_e, fresh_b_ne_d, fresh_b_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0086 :
    d ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_d_not_R, fresh_d_not_A, fresh_d_not_X, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0087 : d ∉ ((Wff.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_e, fresh_d_not_A, fresh_d_ne_x, fresh_d_ne_y,
          fresh_d_not_R, or_false, not_false_eq_true])
  have dv_cache_0088 : d ∉ ((syn_cfpiv R A (.cv x) (.cv y))).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_not_A, fresh_d_ne_x, fresh_d_ne_y, fresh_d_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0089 : d ∉ ((syn_csn (.cv e))).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_d_ne_e,
          not_false_eq_true])
  have dv_cache_0090 :
    y ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))).fv :=
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
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_A, fresh_y_not_X, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0091 : y ∉ ((Wff.classMem (.cv q) (syn_cfdpivrange2 R A X))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, Finset.mem_singleton, fresh_y_ne_q, fresh_y_not_A,
          fresh_y_not_X, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0092 :
    x ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_A, fresh_x_not_X, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0093 : x ∉ ((Wff.classMem (.cv q) (syn_cfdpivrange2 R A X))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_A,
          fresh_x_not_X, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0094 :
    e ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))).fv :=
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
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_e_not_R, fresh_e_not_A, fresh_e_not_X, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0095 : e ∉ ((Wff.classMem (.cv q) (syn_cfdpivrange2 R A X))).fv :=
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
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, Finset.mem_singleton, fresh_e_ne_q, fresh_e_not_A,
          fresh_e_not_X, fresh_e_not_R, or_false, not_false_eq_true])
  have dv_cache_0096 : q ∉ ((syn_cpw1 (syn_cfdif R A X))).fv :=
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
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_X, fresh_q_not_R, or_false, not_false_eq_true])
  have dv_cache_0097 : q ∉ ((syn_cfdpivrange2 R A X)).fv :=
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
      dv_cache_0096
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_q_not_A, fresh_q_not_X, fresh_q_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0098 :
    q ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))).fv :=
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
      dv_cache_0096 dv_cache_0097
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_q_not_R, fresh_q_not_A, fresh_q_not_X, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0099 : x ∉ ((syn_cpw1 (syn_cfdif R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_X, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0100 : y ∉ ((syn_cpw1 (syn_cfdif R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_X, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0101 : y ∉ ((syn_cfdpivrange2 R A X)).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_X, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0102 : x ∉ ((syn_cnc (syn_cpw1 (syn_cfdif R A X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_X, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0103 : x ∉ ((syn_cnc (syn_cfdpivrange2 R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_X, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0104 : y ∉ ((syn_cnc (syn_cfdpivrange2 R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_X, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0105 : x ∉ ((syn_wss (syn_cpw1 (syn_cfdif R A X)) (.cv y))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_not_X, fresh_x_not_R, fresh_x_ne_y,
          or_false, not_false_eq_true])
  have dv_cache_0106 :
    y ∉ ((syn_wss (syn_cpw1 (syn_cfdif R A X)) (syn_cfdpivrange2 R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_X, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0107 : p ∉ ((syn_cnc (syn_cpw1 (syn_cfdif R A X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_X, fresh_p_not_R, or_false, not_false_eq_true])
  have dv_cache_0108 : p ∉ ((syn_cnc (syn_chnord X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_p_not_X,
          not_false_eq_true])
  have dv_cache_0109 : q ∉ ((syn_cnc (syn_chnord X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_q_not_X,
          not_false_eq_true])
  have dv_cache_0110 : p ≠ q :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0111 : p ≠ g :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110
    exact (show p ≠ g from (by exact fresh_p_ne_g))
  have dv_cache_0112 : q ≠ g :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111
    exact (show q ≠ g from (by exact fresh_q_ne_g))
  have dv_cache_0113 : h ∉ ((Class.cv p)).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_p, not_false_eq_true])
  have dv_cache_0114 : h ∉ ((syn_cpw1 (syn_cfdif R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_h_not_A, fresh_h_not_X, fresh_h_not_R, or_false, not_false_eq_true])
  have dv_cache_0115 : i ∉ ((Class.cv q)).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_i_ne_q, not_false_eq_true])
  have dv_cache_0116 : i ∉ ((syn_chnord X)).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_i_not_X, not_false_eq_true])
  have dv_cache_0117 : i ∉ ((syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_i_ne_p, fresh_i_not_A, fresh_i_not_X, fresh_i_not_R,
          fresh_i_ne_h, or_false, not_false_eq_true])
  have dv_cache_0118 : h ∉ ((syn_wf1o (.cv i) (.cv q) (syn_chnord X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_q, fresh_h_not_X, fresh_h_ne_i, or_false,
          not_false_eq_true])
  have dv_cache_0119 :
    f ∉ ((syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_i, fresh_f_ne_g, fresh_f_ne_h, or_false,
          not_false_eq_true])
  have dv_cache_0120 :
    f ∉
      ((syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))
          (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_f_not_A, fresh_f_not_X, fresh_f_not_R, fresh_f_ne_i,
          fresh_f_ne_g, fresh_f_ne_h, or_false, not_false_eq_true])
  have dv_cache_0121 :
    h ∉
      ((Wff.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f
            (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_h_ne_p, fresh_h_ne_q,
          fresh_h_ne_g, fresh_h_not_A, fresh_h_not_X, fresh_h_not_R, fresh_h_ne_f,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0122 :
    i ∉
      ((Wff.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f
            (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_i_ne_p, fresh_i_ne_q,
          fresh_i_ne_g, fresh_i_not_A, fresh_i_not_X, fresh_i_not_R, fresh_i_ne_f,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0123 :
    g ∉ ((syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_X,
          fresh_g_not_R, fresh_g_ne_f, or_false, and_false, not_false_eq_true])
  have dv_cache_0124 :
    g ∉
      ((syn_wa (.classMem (.cv p) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
          (.classMem (.cv q) (syn_cnc (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_p, fresh_g_not_A, fresh_g_not_X, fresh_g_not_R,
          fresh_g_ne_q, or_false, not_false_eq_true])
  have dv_cache_0125 : q ∉ ((syn_cnc (syn_cpw1 (syn_cfdif R A X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_X, fresh_q_not_R, or_false, not_false_eq_true])
  have dv_cache_0126 :
    p ∉ ((syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_X,
          fresh_p_not_R, fresh_p_ne_f, or_false, and_false, not_false_eq_true])
  have dv_cache_0127 :
    q ∉ ((syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_X,
          fresh_q_not_R, fresh_q_ne_f, or_false, and_false, not_false_eq_true])
  have dv_cache_0128 : f ∉ ((Wff.classEq (.cv a) (syn_cpw1 (syn_cfdif R A X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_a, fresh_f_not_A, fresh_f_not_X, fresh_f_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0129 : f ∉ ((Wff.classEq (.cv b) (syn_chnord X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_b, fresh_f_not_X, or_false, not_false_eq_true])
  have dv_cache_0130 : a ∉ ((syn_cpw1 (syn_cfdif R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_a_not_A, fresh_a_not_X, fresh_a_not_R, or_false, not_false_eq_true])
  have dv_cache_0131 : b ∉ ((syn_cpw1 (syn_cfdif R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_X, fresh_b_not_R, or_false, not_false_eq_true])
  have dv_cache_0132 : b ∉ ((syn_chnord X)).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_b_not_X, not_false_eq_true])
  have dv_cache_0133 : a ∉ ((syn_cnc (syn_cpw1 (syn_cfdif R A X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_a_not_A, fresh_a_not_X, fresh_a_not_R, or_false, not_false_eq_true])
  have dv_cache_0134 : a ∉ ((syn_cnc (syn_chnord X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_a_not_X,
          not_false_eq_true])
  have dv_cache_0135 : b ∉ ((syn_cnc (syn_chnord X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_b_not_X,
          not_false_eq_true])
  have dv_cache_0136 :
    a ∉ ((syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (.cv b)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_A, fresh_a_not_X,
          fresh_a_not_R, fresh_a_ne_b, fresh_a_ne_f, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0137 :
    b ∉ ((syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_X,
          fresh_b_not_R, fresh_b_ne_f, or_false, and_false, not_false_eq_true])
  have dv_cache_0138 : a ≠ f :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
    exact (show a ≠ f from (by exact fresh_a_ne_f))
  have dv_cache_0139 : b ≠ f :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138
    exact (show b ≠ f from (by exact fresh_b_ne_f))
  have dv_cache_0140 : f ∉ ((syn_cpw1 (syn_cfdif R A X))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_f_not_A, fresh_f_not_X, fresh_f_not_R, or_false, not_false_eq_true])
  have dv_cache_0141 : f ∉ ((syn_chnord X)).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_f_not_X, not_false_eq_true])
  have dv_cache_0142 : h ∉ ((syn_chnord X)).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_h_not_X, not_false_eq_true])
  have dv_cache_0143 : f ≠ h :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142
    exact (show f ≠ h from (by exact fresh_f_ne_h))
  have dv_cache_0144 :
    p ∉ ((syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_X, fresh_p_not_R, or_false, not_false_eq_true])
  have dv_cache_0145 : p ∉ ((syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_p_not_X,
          not_false_eq_true])
  have dv_cache_0146 : q ∉ ((syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_q_not_X,
          not_false_eq_true])
  have dv_cache_0147 : a ∉ ((Class.cv p)).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_p, not_false_eq_true])
  have dv_cache_0148 : a ∉ ((syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_a_not_A, fresh_a_not_X, fresh_a_not_R, or_false, not_false_eq_true])
  have dv_cache_0149 : i ∉ ((syn_cpw (syn_cpw (syn_chnord X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_i_not_X,
          not_false_eq_true])
  have dv_cache_0150 :
    i ∉
      ((syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_i_ne_p, fresh_i_not_A, fresh_i_not_X, fresh_i_not_R,
          fresh_i_ne_a, or_false, not_false_eq_true])
  have dv_cache_0151 :
    a ∉ ((syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_q, fresh_a_not_X, fresh_a_ne_i, or_false,
          not_false_eq_true])
  have dv_cache_0152 :
    h ∉ ((syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv a)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_i, fresh_h_ne_g, fresh_h_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0153 :
    h ∉
      ((syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv a)))
          (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
          (syn_cpw (syn_cpw (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_h_not_A, fresh_h_not_X, fresh_h_not_R, fresh_h_ne_i,
          fresh_h_ne_g, fresh_h_ne_a, or_false, not_false_eq_true])
  have dv_cache_0154 :
    a ∉
      ((Wff.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex h
            (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
              (syn_cpw (syn_cpw (syn_chnord X))))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_q,
          fresh_a_ne_g, fresh_a_not_A, fresh_a_not_X, fresh_a_not_R, fresh_a_ne_h,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0155 :
    i ∉
      ((Wff.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex h
            (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
              (syn_cpw (syn_cpw (syn_chnord X))))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154
    exact
      (by
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_i_ne_p, fresh_i_ne_q,
          fresh_i_ne_g, fresh_i_not_A, fresh_i_not_X, fresh_i_not_R, fresh_i_ne_h,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0156 :
    g ∉
      ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_X,
          fresh_g_not_R, fresh_g_ne_h, or_false, and_false, not_false_eq_true])
  have dv_cache_0157 :
    g ∉
      ((syn_wa (.classMem (.cv p) (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
          (.classMem (.cv q) (syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_p, fresh_g_not_A, fresh_g_not_X, fresh_g_not_R,
          fresh_g_ne_q, or_false, not_false_eq_true])
  have dv_cache_0158 :
    q ∉ ((syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_X, fresh_q_not_R, or_false, not_false_eq_true])
  have dv_cache_0159 :
    p ∉
      ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_X,
          fresh_p_not_R, fresh_p_ne_h, or_false, and_false, not_false_eq_true])
  have dv_cache_0160 :
    q ∉
      ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_X,
          fresh_q_not_R, fresh_q_ne_h, or_false, and_false, not_false_eq_true])
  have dv_cache_0161 :
    h ∉ ((Wff.classEq (.cv b) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_b, fresh_h_not_A, fresh_h_not_X, fresh_h_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0162 :
    h ∉ ((Wff.classEq (.cv c) (syn_cpw (syn_cpw (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_c, fresh_h_not_X, or_false, not_false_eq_true])
  have dv_cache_0163 : b ∉ ((syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_X, fresh_b_not_R, or_false, not_false_eq_true])
  have dv_cache_0164 : c ∉ ((syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_c_not_A, fresh_c_not_X, fresh_c_not_R, or_false, not_false_eq_true])
  have dv_cache_0165 : c ∉ ((syn_cpw (syn_cpw (syn_chnord X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_c_not_X,
          not_false_eq_true])
  have dv_cache_0166 :
    b ∉ ((syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_X, fresh_b_not_R, or_false, not_false_eq_true])
  have dv_cache_0167 : b ∉ ((syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_b_not_X,
          not_false_eq_true])
  have dv_cache_0168 : c ∉ ((syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166 dv_cache_0167
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_c_not_X,
          not_false_eq_true])
  have dv_cache_0169 :
    b ∉
      ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
            (.cv c)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166 dv_cache_0167
      dv_cache_0168
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_X,
          fresh_b_not_R, fresh_b_ne_c, fresh_b_ne_h, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0170 :
    c ∉
      ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166 dv_cache_0167
      dv_cache_0168 dv_cache_0169
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_not_A, fresh_c_not_X,
          fresh_c_not_R, fresh_c_ne_h, or_false, and_false, not_false_eq_true])
  have dv_cache_0171 : b ≠ c :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166 dv_cache_0167
      dv_cache_0168 dv_cache_0169 dv_cache_0170
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0172 : b ≠ h :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166 dv_cache_0167
      dv_cache_0168 dv_cache_0169 dv_cache_0170 dv_cache_0171
    exact (show b ≠ h from (by exact fresh_b_ne_h))
  have dv_cache_0173 : c ≠ h :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166 dv_cache_0167
      dv_cache_0168 dv_cache_0169 dv_cache_0170 dv_cache_0171 dv_cache_0172
    exact (show c ≠ h from (by exact fresh_c_ne_h))
  have dv_cache_0174 : k ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 A)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166 dv_cache_0167
      dv_cache_0168 dv_cache_0169 dv_cache_0170 dv_cache_0171 dv_cache_0172 dv_cache_0173
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_A_k,
          not_false_eq_true])
  have dv_cache_0175 : k ∉ ((syn_cpw (syn_cpw (syn_chnord X)))).fv :=
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
      dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
      dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
      dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
      dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
      dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
      dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
      dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
      dv_cache_0150 dv_cache_0151 dv_cache_0152 dv_cache_0153 dv_cache_0154 dv_cache_0155
      dv_cache_0156 dv_cache_0157 dv_cache_0158 dv_cache_0159 dv_cache_0160 dv_cache_0161
      dv_cache_0162 dv_cache_0163 dv_cache_0164 dv_cache_0165 dv_cache_0166 dv_cache_0167
      dv_cache_0168 dv_cache_0169 dv_cache_0170 dv_cache_0171 dv_cache_0172 dv_cache_0173
      dv_cache_0174
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, dv_X_k,
          not_false_eq_true])
  let syntaxFormula0000 : Wff :=
    (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))))
  let syntaxFormula0001 : Wff :=
    (syn_wbr (syn_ctc (syn_ctc (syn_cnc A))) (syn_clec)
      (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X)))))
  let syntaxFormula0002 : Wff :=
    (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_cnc A)))) (syn_clec)
      (syn_ctc (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X))))))
  let syntaxFormula0003 : Wff :=
    (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))
      (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))))
  let syntaxFormula0004 : Wff :=
    (syn_wrex z (syn_cpw (syn_cpw (syn_cfdif R A X))) (.classEq (.cv x) (syn_cpw1 (.cv z))))
  let syntaxFormula0005 : Wff :=
    (syn_wrex y (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))
      (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
  let syntaxFormula0006 : Wff :=
    (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
  let syntaxFormula0007 : Wff :=
    (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
  let syntaxFormula0008 : Wff :=
    (syn_wrex z (syn_cpw (syn_cpw (syn_cfdif R A X))) syntaxFormula0007)
  let syntaxFormula0009 : Wff := (syn_wex y syntaxFormula0007)
  let syntaxFormula0010 : Wff :=
    (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))
      (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X)))))
  let syntaxFormula0011 : Wff :=
    (.classMem (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_cvv))
  let syntaxFormula0012 : Wff :=
    (syn_wbr (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cen)
      (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X)))))
  let syntaxFormula0013 : Wff :=
    (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (syn_cpw1 (syn_cpw (syn_cfdif R A X)))
      (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X)))))
  let syntaxFormula0014 : Wff :=
    (syn_wrex y (syn_cpw1 (syn_cpw (syn_cfdif R A X))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
  let syntaxFormula0015 : Wff :=
    (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
  let syntaxFormula0016 : Wff :=
    (syn_wrex z (syn_cpw (syn_cfdif R A X)) syntaxFormula0007)
  let syntaxFormula0017 : Wff :=
    (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (syn_cpw1 (syn_cpw (syn_cfdif R A X))) (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
  let syntaxFormula0018 : Wff :=
    (.classMem (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X)))) (syn_cvv))
  let syntaxFormula0019 : Wff :=
    (syn_wbr (syn_cpw1 (syn_cpw (syn_cfdif R A X))) (syn_cen)
      (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
  let syntaxFormula0020 : Wff :=
    (syn_wbr (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X)))) (syn_cen)
      (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
  let syntaxFormula0021 : Wff :=
    (syn_wbr (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cen)
      (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
  let syntaxFormula0022 : Wff :=
    (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_cnc A)))) (syn_clec)
      (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
  let syntaxFormula0023 : Wff :=
    (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))
      (.classMem (.cv e) (syn_cfdif R A X)))
  let syntaxFormula0024 : Wff :=
    (syn_wa syntaxFormula0023 (.classEq (.cv q) (syn_csn (.cv e))))
  let syntaxFormula0025 : Wff :=
    (syn_wrex x X (syn_wrex y X (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))))
  let syntaxFormula0026 : Wff := (syn_wa syntaxFormula0024 (.classMem (.cv x) X))
  let syntaxFormula0027 : Wff :=
    (syn_wa syntaxFormula0024 (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X)))
  let syntaxFormula0028 : Wff :=
    (syn_wa syntaxFormula0027 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))))
  let syntaxFormula0029 : Wff :=
    (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X)))
  let syntaxFormula0030 : Wff :=
    (syn_wa (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csn (.cv e))))
  let syntaxFormula0031 : Wff :=
    (.imp (.classMem (.cv d) (syn_csn (.cv e)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
  let syntaxFormula0032 : Wff :=
    (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv e) R (.cv c)))
  let syntaxFormula0033 : Wff := (syn_wral c A syntaxFormula0032)
  let syntaxFormula0034 : Wff :=
    (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y))))
      syntaxFormula0033)
  let syntaxFormula0035 : Wff :=
    (syn_wa (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
  let syntaxFormula0036 : Wff :=
    (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))
  let syntaxFormula0037 : Wff := (syn_wral c A syntaxFormula0036)
  let syntaxFormula0038 : Wff :=
    (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
      syntaxFormula0037)
  let syntaxFormula0039 : Wff :=
    (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a)))
      (.classEq (.cv a) (.cv b)))
  let syntaxFormula0040 : Wff := (syn_wral b A syntaxFormula0039)
  let syntaxFormula0041 : Wff := (syn_wral a A syntaxFormula0040)
  let syntaxFormula0042 : Wff :=
    (.imp (syn_wa (syn_wbr (.cv e) R (.cv d)) (syn_wbr (.cv d) R (.cv e)))
      (.classEq (.cv e) (.cv d)))
  let syntaxFormula0043 : Wff :=
    (syn_wb (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csn (.cv e))))
  let syntaxFormula0044 : Wff := (.imp syntaxFormula0031 syntaxFormula0043)
  let syntaxFormula0045 : Wff :=
    (.imp (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X)))
  let syntaxFormula0046 : Wff := (.imp (.classMem (.cv y) X) syntaxFormula0045)
  let syntaxFormula0047 : Wff := (syn_wral y X syntaxFormula0045)
  let syntaxFormula0048 : Wff :=
    (.imp (syn_wrex y X (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X)))
  let syntaxFormula0049 : Wff := (.imp (.classMem (.cv x) X) syntaxFormula0048)
  let syntaxFormula0050 : Wff := (syn_wral x X syntaxFormula0048)
  let syntaxFormula0051 : Wff :=
    (.imp (.classEq (.cv q) (syn_csn (.cv e))) (.classMem (.cv q) (syn_cfdpivrange2 R A X)))
  let syntaxFormula0052 : Wff :=
    (.imp (.classMem (.cv e) (syn_cfdif R A X)) syntaxFormula0051)
  let syntaxFormula0053 : Wff := (syn_wral e (syn_cfdif R A X) syntaxFormula0051)
  let syntaxFormula0054 : Wff :=
    (syn_wa (.classMem (syn_cfdpivrange2 R A X) (syn_cnc (syn_cfdpivrange2 R A X)))
      (syn_wss (syn_cpw1 (syn_cfdif R A X)) (syn_cfdpivrange2 R A X)))
  let syntaxFormula0055 : Wff :=
    (syn_wrex x (syn_cnc (syn_cpw1 (syn_cfdif R A X)))
      (syn_wrex y (syn_cnc (syn_cfdpivrange2 R A X)) (syn_wss (.cv x) (.cv y))))
  let syntaxFormula0056 : Wff :=
    (syn_wbr (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_clec)
      (syn_cnc (syn_cfdpivrange2 R A X)))
  let syntaxFormula0057 : Wff :=
    (syn_wbr (syn_cnc (syn_cfdpivrange2 R A X)) (syn_clec)
      (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))))
  let syntaxFormula0058 : Wff := (syn_wa syntaxFormula0056 syntaxFormula0057)
  let syntaxFormula0059 : Wff :=
    (syn_wa (.classMem (syn_cnc (syn_cfdpivrange2 R A X)) (syn_cncs))
      (.classMem (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs)))
  let syntaxFormula0060 : Wff := (.imp syntaxFormula0059 syntaxFormula0059)
  let syntaxFormula0061 : Wff :=
    (syn_wbr (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_clec)
      (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))))
  let syntaxFormula0062 : Wff := (.imp syntaxFormula0058 syntaxFormula0061)
  let syntaxFormula0063 : Wff :=
    (syn_wbr (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_clec)
      (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))))
  let syntaxFormula0064 : Wff :=
    (syn_wbr (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X))))) (syn_clec)
      (syn_ctc (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))))))
  let syntaxFormula0065 : Wff :=
    (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))))
      (syn_chwcards (syn_cvv)))
  let syntaxFormula0066 : Wff :=
    (syn_wbr (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X))))) (syn_clec)
      (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))))
  let syntaxFormula0067 : Wff :=
    (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
      (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X))))))
  let syntaxFormula0068 : Wff := (syn_wo syntaxFormula0066 syntaxFormula0067)
  let syntaxFormula0069 : Wff :=
    (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X))))) (syn_cncs))
  let syntaxFormula0070 : Wff :=
    (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))))) (syn_cncs))
  let syntaxFormula0071 : Wff :=
    (syn_w3a (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs))
      syntaxFormula0069 syntaxFormula0070)
  let syntaxFormula0072 : Wff :=
    (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
      (syn_ctc (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))))))
  let syntaxFormula0073 : Wff := (.neg syntaxFormula0067)
  let syntaxFormula0074 : Wff := (.neg syntaxFormula0073)
  let syntaxFormula0075 : Wff := (.neg syntaxFormula0072)
  let syntaxFormula0076 : Wff := (.neg syntaxFormula0066)
  let syntaxFormula0077 : Wff := (.imp syntaxFormula0064 syntaxFormula0066)
  let syntaxFormula0078 : Wff := (.neg syntaxFormula0077)
  let syntaxFormula0079 : Wff := (.neg syntaxFormula0078)
  let syntaxFormula0080 : Wff := (.imp syntaxFormula0078 syntaxFormula0066)
  let syntaxFormula0081 : Wff := (.imp syntaxFormula0066 syntaxFormula0077)
  let syntaxFormula0082 : Wff := (.imp syntaxFormula0078 syntaxFormula0077)
  let syntaxFormula0083 : Wff :=
    (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
      (syn_ctc (syn_ctc (syn_chncard X))))
  let syntaxFormula0084 : Wff := (syn_wa syntaxFormula0066 syntaxFormula0083)
  let syntaxFormula0085 : Wff :=
    (syn_wa (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_chncard X))) (syn_cncs)))
  let syntaxFormula0086 : Wff := (.imp syntaxFormula0085 syntaxFormula0085)
  let syntaxFormula0087 : Wff :=
    (syn_wbr (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X))))) (syn_clec)
      (syn_ctc (syn_ctc (syn_chncard X))))
  let syntaxFormula0088 : Wff := (.imp syntaxFormula0084 syntaxFormula0087)
  let syntaxFormula0089 : Wff :=
    (syn_wbr (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_clec)
      (syn_ctc (syn_chncard X)))
  let syntaxFormula0090 : Wff :=
    (syn_wbr (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_clec) (syn_cnc (syn_chnord X)))
  let syntaxFormula0091 : Wff :=
    (syn_wa (.classMem (.cv p) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      (.classMem (.cv q) (syn_cnc (syn_chnord X))))
  let syntaxFormula0092 : Wff :=
    (syn_wa (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1o (.cv i) (.cv q) (syn_chnord X)))
  let syntaxFormula0093 : Wff :=
    (syn_w3a (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1o (.cv i) (.cv q) (syn_chnord X)) (syn_wf1 (.cv g) (.cv p) (.cv q)))
  let syntaxFormula0094 : Wff :=
    (syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))
      (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))
  let syntaxFormula0095 : Wff :=
    (syn_wa (.classMem (syn_chnord X) (syn_cnc (syn_chnord X)))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))))
  let syntaxFormula0096 : Wff :=
    (syn_wrex b (syn_cnc (syn_chnord X)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))
  let syntaxFormula0097 : Wff :=
    (syn_wrex a (syn_cnc (syn_cpw1 (syn_cfdif R A X))) syntaxFormula0096)
  let syntaxFormula0098 : Wff :=
    (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
      (syn_cpw (syn_cpw (syn_chnord X))))
  let syntaxFormula0099 : Wff := (syn_wex h syntaxFormula0098)
  let syntaxFormula0100 : Wff :=
    (.classMem (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))) (syn_cncs))
  let syntaxFormula0101 : Wff :=
    (syn_wbr (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))) (syn_clec)
      (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))))
  let syntaxFormula0102 : Wff :=
    (syn_wrex p (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wrex q (syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))
        (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q)))))
  let syntaxFormula0103 : Wff :=
    (syn_wa (.classMem (.cv p) (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
      (.classMem (.cv q) (syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))))
  let syntaxFormula0104 : Wff :=
    (syn_wa (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X)))))
  let syntaxFormula0105 : Wff := (syn_wex a (syn_wex i syntaxFormula0104))
  let syntaxFormula0106 : Wff :=
    (syn_w3a (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv g) (.cv p) (.cv q)))
  let syntaxFormula0107 : Wff :=
    (syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv a)))
      (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (syn_cpw (syn_cpw (syn_chnord X))))
  let syntaxFormula0108 : Wff :=
    (.classMem (syn_cpw (syn_cpw (syn_chnord X))) (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))))
  let syntaxFormula0109 : Wff := (syn_wa syntaxFormula0108 syntaxFormula0099)
  let syntaxFormula0110 : Wff :=
    (.classMem (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
      (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
  let syntaxFormula0111 : Wff :=
    (syn_wrex c (syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wex h (syn_wf1 (.cv h) (.cv b) (.cv c))))
  let syntaxFormula0112 : Wff :=
    (syn_wrex b (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))) syntaxFormula0111)
  let syntaxFormula0113 : Wff := (syn_wa syntaxFormula0022 syntaxFormula0101)
  let syntaxFormula0114 : Wff :=
    (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_cnc A)))) (syn_clec)
      (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))))
  let syntaxFormula0115 : Wff := (.imp syntaxFormula0113 syntaxFormula0114)
  have p0000 :=
    @g_fdcolcodetc2le2 A X R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0001 := @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))
  have p0002 := @g_id (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
  have p0003 :=
    @g_a1ii
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wbr R (syn_cwe) A))
      syntaxFormula0000 p0001 p0002
  have p0004 := @g_simpr (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))
  have p0005 :=
    @g_a1ii
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wss A (syn_cpw X)))
      syntaxFormula0000 p0004 p0002
  have p0006 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)) p0003 p0005
  have p0007 :=
    @g_a1ii
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0001)
      syntaxFormula0000 p0000 p0006
  have p0008 :=
    @g_fdifex2 A X R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_cfbfdwppcarrierimpndv_1
      hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0009 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdif R A X) (syn_cvv)) p0003 p0008
  have p0010 := @g_pwexg (syn_cfdif R A X) (syn_cvv)
  have p0011 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cfdif R A X) (syn_cvv))
      (.classMem (syn_cpw (syn_cfdif R A X)) (syn_cvv)) p0009 p0010
  have p0012 := @g_pwexg (syn_cpw (syn_cfdif R A X)) (syn_cvv)
  have p0013 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw (syn_cfdif R A X)) (syn_cvv))
      (.classMem (syn_cpw (syn_cpw (syn_cfdif R A X))) (syn_cvv)) p0011 p0012
  have p0014 := @g_ncelncs (syn_cpw (syn_cpw (syn_cfdif R A X))) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw (syn_cpw (syn_cfdif R A X))) (syn_cvv))
      (.classMem (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cncs)) p0013 p0014
  have p0016 := @g_ncelncs A (syn_cvv)
  have p0017 := Nominal.mp hyp_cfbfdwppcarrierimpndv_2 p0016
  have p0018 := @g_tccl (syn_cnc A)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 := @g_tccl (syn_ctc (syn_cnc A))
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @g_jctil (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_cnc A))) (syn_cncs)) p0015 p0021
  have p0023 :=
    @g_tlecg (syn_ctc (syn_ctc (syn_cnc A)))
      (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X))))
  have p0024 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa (.classMem (syn_ctc (syn_ctc (syn_cnc A))) (syn_cncs))
        (.classMem (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cncs)))
      (syn_wb syntaxFormula0001 syntaxFormula0002) p0022 p0023
  have p0025 :=
    @g_mpbid (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0001
      syntaxFormula0002 p0007 p0024
  have p0026 := @g_tcncg (syn_cpw (syn_cpw (syn_cfdif R A X))) (syn_cvv)
  have p0027 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw (syn_cpw (syn_cfdif R A X))) (syn_cvv))
      (.classEq (syn_ctc (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X)))))
        (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))))
      p0013 p0026
  have p0028 := @g_pw1fnf1o
  have p0029 := @g_f1of1 (syn_c1c) (syn_cpw (syn_c1c)) (syn_cpw1fn)
  have p0030 := Nominal.mp p0028 p0029
  have p0031 := @g_pw1ss1c (syn_cpw (syn_cpw (syn_cfdif R A X)))
  have p0032 :=
    @g_f1ores (syn_c1c) (syn_cpw (syn_c1c))
      (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cpw1fn)
  have p0033 :=
    @g_mp2an (syn_wf1 (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c)))
      (syn_wss (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_c1c))
      syntaxFormula0003 p0030 p0031 p0032
  have p0034 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y (syn_cpw1fn)
      (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0035 := @g_vex x
  have p0036 := @g_elpw (.cv x) (syn_cpw1 (syn_cpw (syn_cfdif R A X))) p0035
  have p0037 :=
    @g_sspw1 z (.cv x) (syn_cpw (syn_cfdif R A X)) dv_cache_0009 dv_cache_0010 p0035
  have p0038 := (Nominal.biimpRefl syntaxFormula0004)
  have p0039 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw z
      (syn_cpw (syn_cfdif R A X)) dv_cache_0010
  have p0040 :=
    @g_eqabri (syn_wss (.cv z) (syn_cpw (syn_cfdif R A X))) z
      (syn_cpw (syn_cpw (syn_cfdif R A X))) p0039
  have p0041 :=
    @g_anbi1i (.classMem (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A X))))
      (syn_wss (.cv z) (syn_cpw (syn_cfdif R A X))) (.classEq (.cv x) (syn_cpw1 (.cv z)))
      p0040
  have p0042 :=
    @g_exbii
      (syn_wa (.classMem (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A X))))
        (.classEq (.cv x) (syn_cpw1 (.cv z))))
      (syn_wa (syn_wss (.cv z) (syn_cpw (syn_cfdif R A X)))
        (.classEq (.cv x) (syn_cpw1 (.cv z))))
      z p0041
  have p0043 :=
    @g_bitr2i syntaxFormula0004
      (syn_wex z (syn_wa (.classMem (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A X))))
          (.classEq (.cv x) (syn_cpw1 (.cv z)))))
      (syn_wex z (syn_wa (syn_wss (.cv z) (syn_cpw (syn_cfdif R A X)))
          (.classEq (.cv x) (syn_cpw1 (.cv z)))))
      p0038 p0042
  have p0044 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X)))))
      (syn_wss (.cv x) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (syn_wex z (syn_wa (syn_wss (.cv z) (syn_cpw (syn_cfdif R A X)))
          (.classEq (.cv x) (syn_cpw1 (.cv z)))))
      syntaxFormula0004 p0036 p0037 p0043
  have p0045 := (Nominal.biimpRefl syntaxFormula0005)
  have p0046 :=
    @g_elpw1 z (.cv y) (syn_cpw (syn_cpw (syn_cfdif R A X))) dv_cache_0011 dv_cache_0012
  have p0047 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_wrex z (syn_cpw (syn_cpw (syn_cfdif R A X))) (.classEq (.cv y) (syn_csn (.cv z))))
      (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)) p0046
  have p0048 :=
    @g_r19_41v (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))
      z (syn_cpw (syn_cpw (syn_cfdif R A X))) dv_cache_0013
  have p0049 :=
    @g_bitr4i syntaxFormula0006
      (syn_wa (syn_wrex z (syn_cpw (syn_cpw (syn_cfdif R A X)))
          (.classEq (.cv y) (syn_csn (.cv z)))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
      syntaxFormula0008 p0047 p0048
  have p0050 := @g_exbii syntaxFormula0006 syntaxFormula0008 y p0049
  have p0051 :=
    @g_rexcom4 syntaxFormula0007 z y (syn_cpw (syn_cpw (syn_cfdif R A X))) dv_cache_0014
      dv_cache_0015
  have p0052 := @g_snex (.cv z)
  have p0053 := @g_breq1 (.cv y) (syn_csn (.cv z)) (.cv x) (syn_cpw1fn)
  have p0054 :=
    @g_ceqsexv (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))
      (syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x)) y (syn_csn (.cv z)) dv_cache_0016
      dv_cache_0017 p0052 p0053
  have p0055 := @g_vex z
  have p0056 := @g_brpw1fn (.cv z) (.cv x) p0055
  have p0057 :=
    @g_bitri syntaxFormula0009 (syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x))
      (.classEq (.cv x) (syn_cpw1 (.cv z))) p0054 p0056
  have p0058 :=
    @g_rexbii syntaxFormula0009 (.classEq (.cv x) (syn_cpw1 (.cv z))) z
      (syn_cpw (syn_cpw (syn_cfdif R A X))) p0057
  have p0059 :=
    @g_bitr3i (syn_wex y syntaxFormula0008)
      (syn_wrex z (syn_cpw (syn_cpw (syn_cfdif R A X))) syntaxFormula0009)
      syntaxFormula0004 p0051 p0058
  have p0060 :=
    @g_n_3bitri syntaxFormula0005 (syn_wex y syntaxFormula0006)
      (syn_wex y syntaxFormula0008) syntaxFormula0004 p0045 p0050 p0059
  have p0061 :=
    @g_bitr4i (.classMem (.cv x) (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X)))))
      syntaxFormula0004 syntaxFormula0005 p0044 p0060
  have p0062 :=
    @g_eqabi syntaxFormula0005 x (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      dv_cache_0018 p0061
  have p0063 :=
    @g_eqtr4i (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (.cab x syntaxFormula0005) (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X)))) p0034
      p0062
  have p0064 :=
    @g_f1oeq3 (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))
      (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
  have p0065 := Nominal.mp p0063 p0064
  have p0066 := @g_mpbi syntaxFormula0003 syntaxFormula0010 p0033 p0065
  have p0067 := @g_id syntaxFormula0010
  have p0068 := @g_pw1fnex
  have p0069 := @g_pw1exg (syn_cpw (syn_cpw (syn_cfdif R A X))) (syn_cvv)
  have p0070 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw (syn_cpw (syn_cfdif R A X))) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cvv)) p0013 p0069
  have p0071 :=
    @g_resexg (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cvv)
      (syn_cvv)
  have p0072 :=
    @g_sylancr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1fn) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cvv))
      syntaxFormula0011 p0068 p0070 p0071
  have p0073 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0011
      syntaxFormula0010 p0072
  have p0074 :=
    @g_f1oeng (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))
      (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X)))) (syn_cvv)
      (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
  have p0075 := @g_ex syntaxFormula0011 syntaxFormula0010 syntaxFormula0012 p0074
  have p0076 :=
    @g_syl56 syntaxFormula0010 syntaxFormula0010
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0011
      (.imp syntaxFormula0010 syntaxFormula0012) p0067 p0073 p0075
  have p0077 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0010
      syntaxFormula0012 p0076
  have p0078 :=
    @g_mpi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0010
      syntaxFormula0012 p0066 p0077
  have p0082 := @g_pw1ss1c (syn_cpw (syn_cfdif R A X))
  have p0083 :=
    @g_f1ores (syn_c1c) (syn_cpw (syn_c1c)) (syn_cpw1 (syn_cpw (syn_cfdif R A X)))
      (syn_cpw1fn)
  have p0084 :=
    @g_mp2an (syn_wf1 (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c)))
      (syn_wss (syn_cpw1 (syn_cpw (syn_cfdif R A X))) (syn_c1c)) syntaxFormula0013 p0030
      p0082 p0083
  have p0085 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y (syn_cpw1fn)
      (syn_cpw1 (syn_cpw (syn_cfdif R A X))) dv_cache_0004 dv_cache_0005 dv_cache_0019
      dv_cache_0020 dv_cache_0008
  have p0087 := @g_elpw (.cv x) (syn_cpw1 (syn_cfdif R A X)) p0035
  have p0088 := @g_sspw1 z (.cv x) (syn_cfdif R A X) dv_cache_0009 dv_cache_0021 p0035
  have p0089 :=
    (Nominal.biimpRefl
      (syn_wrex z (syn_cpw (syn_cfdif R A X)) (.classEq (.cv x) (syn_cpw1 (.cv z)))))
  have p0090 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw z
      (syn_cfdif R A X) dv_cache_0021
  have p0091 :=
    @g_eqabri (syn_wss (.cv z) (syn_cfdif R A X)) z (syn_cpw (syn_cfdif R A X)) p0090
  have p0092 :=
    @g_anbi1i (.classMem (.cv z) (syn_cpw (syn_cfdif R A X)))
      (syn_wss (.cv z) (syn_cfdif R A X)) (.classEq (.cv x) (syn_cpw1 (.cv z))) p0091
  have p0093 :=
    @g_exbii
      (syn_wa (.classMem (.cv z) (syn_cpw (syn_cfdif R A X)))
        (.classEq (.cv x) (syn_cpw1 (.cv z))))
      (syn_wa (syn_wss (.cv z) (syn_cfdif R A X)) (.classEq (.cv x) (syn_cpw1 (.cv z)))) z
      p0092
  have p0094 :=
    @g_bitr2i
      (syn_wrex z (syn_cpw (syn_cfdif R A X)) (.classEq (.cv x) (syn_cpw1 (.cv z))))
      (syn_wex z (syn_wa (.classMem (.cv z) (syn_cpw (syn_cfdif R A X)))
          (.classEq (.cv x) (syn_cpw1 (.cv z)))))
      (syn_wex z (syn_wa (syn_wss (.cv z) (syn_cfdif R A X))
          (.classEq (.cv x) (syn_cpw1 (.cv z)))))
      p0089 p0093
  have p0095 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
      (syn_wss (.cv x) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wex z (syn_wa (syn_wss (.cv z) (syn_cfdif R A X))
          (.classEq (.cv x) (syn_cpw1 (.cv z)))))
      (syn_wrex z (syn_cpw (syn_cfdif R A X)) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0087
      p0088 p0094
  have p0096 := (Nominal.biimpRefl syntaxFormula0014)
  have p0097 := @g_elpw1 z (.cv y) (syn_cpw (syn_cfdif R A X)) dv_cache_0011 dv_cache_0010
  have p0098 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (syn_wrex z (syn_cpw (syn_cfdif R A X)) (.classEq (.cv y) (syn_csn (.cv z))))
      (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)) p0097
  have p0099 :=
    @g_r19_41v (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))
      z (syn_cpw (syn_cfdif R A X)) dv_cache_0013
  have p0100 :=
    @g_bitr4i syntaxFormula0015
      (syn_wa (syn_wrex z (syn_cpw (syn_cfdif R A X)) (.classEq (.cv y) (syn_csn (.cv z))))
        (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
      syntaxFormula0016 p0098 p0099
  have p0101 := @g_exbii syntaxFormula0015 syntaxFormula0016 y p0100
  have p0102 :=
    @g_rexcom4 syntaxFormula0007 z y (syn_cpw (syn_cfdif R A X)) dv_cache_0022
      dv_cache_0015
  have p0109 :=
    @g_rexbii syntaxFormula0009 (.classEq (.cv x) (syn_cpw1 (.cv z))) z
      (syn_cpw (syn_cfdif R A X)) p0057
  have p0110 :=
    @g_bitr3i (syn_wex y syntaxFormula0016)
      (syn_wrex z (syn_cpw (syn_cfdif R A X)) syntaxFormula0009)
      (syn_wrex z (syn_cpw (syn_cfdif R A X)) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0102
      p0109
  have p0111 :=
    @g_n_3bitri syntaxFormula0014 (syn_wex y syntaxFormula0015)
      (syn_wex y syntaxFormula0016)
      (syn_wrex z (syn_cpw (syn_cfdif R A X)) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0096
      p0101 p0110
  have p0112 :=
    @g_bitr4i (.classMem (.cv x) (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
      (syn_wrex z (syn_cpw (syn_cfdif R A X)) (.classEq (.cv x) (syn_cpw1 (.cv z))))
      syntaxFormula0014 p0095 p0111
  have p0113 :=
    @g_eqabi syntaxFormula0014 x (syn_cpw (syn_cpw1 (syn_cfdif R A X))) dv_cache_0023
      p0112
  have p0114 :=
    @g_eqtr4i (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (.cab x syntaxFormula0014) (syn_cpw (syn_cpw1 (syn_cfdif R A X))) p0085 p0113
  have p0115 :=
    @g_f1oeq3 (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (syn_cpw (syn_cpw1 (syn_cfdif R A X))) (syn_cpw1 (syn_cpw (syn_cfdif R A X)))
      (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
  have p0116 := Nominal.mp p0114 p0115
  have p0117 := @g_mpbi syntaxFormula0013 syntaxFormula0017 p0084 p0116
  have p0118 := @g_id syntaxFormula0017
  have p0120 := @g_pw1exg (syn_cpw (syn_cfdif R A X)) (syn_cvv)
  have p0121 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw (syn_cfdif R A X)) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cpw (syn_cfdif R A X))) (syn_cvv)) p0011 p0120
  have p0122 :=
    @g_resexg (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X))) (syn_cvv) (syn_cvv)
  have p0123 :=
    @g_sylancr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1fn) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cpw (syn_cfdif R A X))) (syn_cvv)) syntaxFormula0018 p0068
      p0121 p0122
  have p0124 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0018
      syntaxFormula0017 p0123
  have p0125 :=
    @g_f1oeng (syn_cpw1 (syn_cpw (syn_cfdif R A X)))
      (syn_cpw (syn_cpw1 (syn_cfdif R A X))) (syn_cvv)
      (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
  have p0126 := @g_ex syntaxFormula0018 syntaxFormula0017 syntaxFormula0019 p0125
  have p0127 :=
    @g_syl56 syntaxFormula0017 syntaxFormula0017
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0018
      (.imp syntaxFormula0017 syntaxFormula0019) p0118 p0124 p0126
  have p0128 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0017
      syntaxFormula0019 p0127
  have p0129 :=
    @g_mpi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0017
      syntaxFormula0019 p0117 p0128
  have p0130 :=
    @g_enpw (syn_cpw1 (syn_cpw (syn_cfdif R A X))) (syn_cpw (syn_cpw1 (syn_cfdif R A X)))
  have p0131 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0019
      syntaxFormula0020 p0129 p0130
  have p0132 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0012
      syntaxFormula0020 p0078 p0131
  have p0133 :=
    @g_entr (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))
      (syn_cpw (syn_cpw1 (syn_cpw (syn_cfdif R A X))))
      (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
  have p0134 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa syntaxFormula0012 syntaxFormula0020) syntaxFormula0021 p0132 p0133
  have p0135 :=
    @g_eqncg (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X))))
      (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (syn_cvv)
  have p0136 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))) (syn_cvv))
      (syn_wb (.classEq (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
          (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))) syntaxFormula0021)
      p0070 p0135
  have p0137 :=
    @g_mpbird (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classEq (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
        (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
      syntaxFormula0021 p0134 p0136
  have p0138 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_ctc (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))) p0027 p0137
  have p0139 :=
    @g_breq2d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_ctc (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A X)))))
      (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_ctc (syn_ctc (syn_ctc (syn_cnc A)))) (syn_clec) p0138
  have p0140 :=
    @g_mpbid (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0002
      syntaxFormula0022 p0025 p0139
  have p0141 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0022
      (syn_wwpp) p0140
  have p0142 := @g_elpw1 e (.cv q) (syn_cfdif R A X) dv_cache_0024 dv_cache_0025
  have p0143 :=
    @g_biimpi (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wrex e (syn_cfdif R A X) (.classEq (.cv q) (syn_csn (.cv e)))) p0142
  have p0144 := @g_nfv (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X))) e dv_cache_0026
  have p0145 := @g_nfri (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X))) e p0144
  have p0146 := @g_simpl syntaxFormula0023 (.classEq (.cv q) (syn_csn (.cv e)))
  have p0147 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))
      (.classMem (.cv e) (syn_cfdif R A X))
  have p0148 :=
    @g_syl syntaxFormula0024 syntaxFormula0023 (.classMem (.cv e) (syn_cfdif R A X)) p0146
      p0147
  have p0149 :=
    @g_elfdif x y A X R e dv_cache_0001 dv_cache_0002 dv_cache_0027 dv_cache_0028
      dv_cache_0029 dv_cache_0003 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0008
  have p0150 :=
    @g_biimpi (.classMem (.cv e) (syn_cfdif R A X))
      (syn_wa (.classMem (.cv e) A) syntaxFormula0025) p0149
  have p0151 := @g_simpr (.classMem (.cv e) A) syntaxFormula0025
  have p0152 :=
    @g_syl (.classMem (.cv e) (syn_cfdif R A X))
      (syn_wa (.classMem (.cv e) A) syntaxFormula0025) syntaxFormula0025 p0150 p0151
  have p0153 :=
    @g_syl syntaxFormula0024 (.classMem (.cv e) (syn_cfdif R A X)) syntaxFormula0025 p0148
      p0152
  have p0154 := @g_nfv syntaxFormula0024 x dv_cache_0038
  have p0155 := @g_nfri syntaxFormula0024 x p0154
  have p0156 := @g_nfv syntaxFormula0026 y dv_cache_0039
  have p0157 := @g_nfri syntaxFormula0026 y p0156
  have p0158 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wbr R (syn_cwe) A) syntaxFormula0028 p0003
  have p0159 :=
    @g_simpl syntaxFormula0027 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0160 :=
    @g_simpr syntaxFormula0024 (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X))
  have p0161 := @g_simpl (.classMem (.cv x) X) (.classMem (.cv y) X)
  have p0162 :=
    @g_syl syntaxFormula0027 (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X))
      (.classMem (.cv x) X) p0160 p0161
  have p0163 :=
    @g_syl syntaxFormula0028 syntaxFormula0027 (.classMem (.cv x) X) p0159 p0162
  have p0166 := @g_simpr (.classMem (.cv x) X) (.classMem (.cv y) X)
  have p0167 :=
    @g_syl syntaxFormula0027 (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X))
      (.classMem (.cv y) X) p0160 p0166
  have p0168 :=
    @g_syl syntaxFormula0028 syntaxFormula0027 (.classMem (.cv y) X) p0159 p0167
  have p0169 :=
    @g_jca syntaxFormula0028 (.classMem (.cv x) X) (.classMem (.cv y) X) p0163 p0168
  have p0170 :=
    @g_pm3_2 (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X))
  have p0171 :=
    @g_syl5 syntaxFormula0028 (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X))
      (syn_wbr R (syn_cwe) A) syntaxFormula0029 p0169 p0170
  have p0172 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (syn_wbr R (syn_cwe) A) (.imp syntaxFormula0028 syntaxFormula0029) p0158 p0171
  have p0173 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      syntaxFormula0029 p0172
  have p0174 :=
    @g_fdpivinrange A X (.cv x) (.cv y) R dv_cache_0001 dv_cache_0040 dv_cache_0041
      dv_cache_0002 dv_cache_0042 dv_cache_0043 dv_cache_0003 dv_cache_0044 dv_cache_0045
      dv_cache_0046 hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2
      hyp_cfbfdwppcarrierimpndv_3
  have p0175 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      syntaxFormula0029
      (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X)) p0173 p0174
  have p0177 :=
    @g_simpl syntaxFormula0024 (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X))
  have p0178 := @g_syl syntaxFormula0028 syntaxFormula0027 syntaxFormula0024 p0159 p0177
  have p0179 := @g_simpr syntaxFormula0023 (.classEq (.cv q) (syn_csn (.cv e)))
  have p0180 :=
    @g_syl syntaxFormula0028 syntaxFormula0024 (.classEq (.cv q) (syn_csn (.cv e))) p0178
      p0179
  have p0181 :=
    @g_simpr syntaxFormula0027 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0182 :=
    @g_simpl (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csn (.cv e)))
  have p0183 :=
    @g_simpr (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csn (.cv e)))
  have p0184 := @g_elsn d (.cv e) dv_cache_0047
  have p0185 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_csn (.cv e))) (.classEq (.cv d) (.cv e)))
      syntaxFormula0030 p0184
  have p0186 :=
    @g_mpbid syntaxFormula0030 (.classMem (.cv d) (syn_csn (.cv e)))
      (.classEq (.cv d) (.cv e)) p0183 p0185
  have p0187 :=
    @g_eleq1d syntaxFormula0030 (.cv d) (.cv e) (syn_cfpiv R A (.cv x) (.cv y)) p0186
  have p0188 :=
    @g_mpbird syntaxFormula0030 (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) p0182 p0187
  have p0189 :=
    @g_ex (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csn (.cv e)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) p0188
  have p0190 :=
    @g_a1d (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0031
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) p0189
  have p0191 :=
    @g_simpl (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0192 :=
    @g_elfpiv A (.cv x) (.cv y) R e c dv_cache_0040 dv_cache_0041 dv_cache_0002
      dv_cache_0048 dv_cache_0027 dv_cache_0044 dv_cache_0045 dv_cache_0049 dv_cache_0050
      dv_cache_0046 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0033 dv_cache_0054
  have p0193 :=
    @g_biimpi (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0034 p0192
  have p0194 :=
    @g_simplr (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y)))
      syntaxFormula0033
  have p0195 :=
    @g_syl (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0034
      (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y))) p0193 p0194
  have p0196 :=
    @g_syl syntaxFormula0035 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y))) p0191 p0195
  have p0200 :=
    @g_simpll (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y)))
      syntaxFormula0033
  have p0201 :=
    @g_syl (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0034
      (.classMem (.cv e) A) p0193 p0200
  have p0202 :=
    @g_syl syntaxFormula0035 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) A) p0191 p0201
  have p0203 :=
    @g_simpr (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0204 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0040 dv_cache_0041 dv_cache_0002
      dv_cache_0048 dv_cache_0055 dv_cache_0044 dv_cache_0045 dv_cache_0049 dv_cache_0056
      dv_cache_0046 dv_cache_0051 dv_cache_0057 dv_cache_0053 dv_cache_0058 dv_cache_0059
  have p0205 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0038 p0204
  have p0206 :=
    @g_simpr
      (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
      syntaxFormula0037
  have p0207 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0038
      syntaxFormula0037 p0205 p0206
  have p0208 :=
    @g_syl syntaxFormula0035 (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      syntaxFormula0037 p0203 p0207
  have p0209 :=
    @g_jca syntaxFormula0035 (.classMem (.cv e) A) syntaxFormula0037 p0202 p0208
  have p0210 := @g_id (.classEq (.cv c) (.cv e))
  have p0211 :=
    @g_eleq1d (.classEq (.cv c) (.cv e)) (.cv c) (.cv e) (syn_csep2 (.cv x) (.cv y)) p0210
  have p0213 := @g_breq2d (.classEq (.cv c) (.cv e)) (.cv c) (.cv e) (.cv d) R p0210
  have p0214 :=
    @g_imbi12d (.classEq (.cv c) (.cv e)) (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
      (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))
      (syn_wbr (.cv d) R (.cv e)) p0211 p0213
  have p0215 :=
    @g_rspcva syntaxFormula0036
      (.imp (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv e))) c
      (.cv e) A dv_cache_0060 dv_cache_0048 dv_cache_0061 p0214
  have p0216 :=
    @g_syl syntaxFormula0035 (syn_wa (.classMem (.cv e) A) syntaxFormula0037)
      (.imp (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv e)))
      p0209 p0215
  have p0217 :=
    @g_mpd syntaxFormula0035 (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y)))
      (syn_wbr (.cv d) R (.cv e)) p0196 p0216
  have p0221 :=
    @g_simplr (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      syntaxFormula0037
  have p0222 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0038
      (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) p0205 p0221
  have p0223 :=
    @g_syl syntaxFormula0035 (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) p0203 p0222
  have p0227 :=
    @g_simpll (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      syntaxFormula0037
  have p0228 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0038
      (.classMem (.cv d) A) p0205 p0227
  have p0229 :=
    @g_syl syntaxFormula0035 (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) A) p0203 p0228
  have p0233 :=
    @g_simpr
      (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y))))
      syntaxFormula0033
  have p0234 :=
    @g_syl (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0034
      syntaxFormula0033 p0193 p0233
  have p0235 :=
    @g_syl syntaxFormula0035 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      syntaxFormula0033 p0191 p0234
  have p0236 :=
    @g_jca syntaxFormula0035 (.classMem (.cv d) A) syntaxFormula0033 p0229 p0235
  have p0237 := @g_id (.classEq (.cv c) (.cv d))
  have p0238 :=
    @g_eleq1d (.classEq (.cv c) (.cv d)) (.cv c) (.cv d) (syn_csep2 (.cv x) (.cv y)) p0237
  have p0240 := @g_breq2d (.classEq (.cv c) (.cv d)) (.cv c) (.cv d) (.cv e) R p0237
  have p0241 :=
    @g_imbi12d (.classEq (.cv c) (.cv d)) (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv e) R (.cv c))
      (syn_wbr (.cv e) R (.cv d)) p0238 p0240
  have p0242 :=
    @g_rspcva syntaxFormula0032
      (.imp (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv e) R (.cv d))) c
      (.cv d) A dv_cache_0062 dv_cache_0048 dv_cache_0063 p0241
  have p0243 :=
    @g_syl syntaxFormula0035 (syn_wa (.classMem (.cv d) A) syntaxFormula0033)
      (.imp (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv e) R (.cv d)))
      p0236 p0242
  have p0244 :=
    @g_mpd syntaxFormula0035 (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (syn_wbr (.cv e) R (.cv d)) p0223 p0243
  have p0245 :=
    @g_a1d syntaxFormula0035 (syn_wbr (.cv e) R (.cv d)) (syn_wbr (.cv d) R (.cv e)) p0244
  have p0246 := @g_ancom (syn_wbr (.cv d) R (.cv e)) (syn_wbr (.cv e) R (.cv d))
  have p0247 := @g_wppweantisym A R
  have p0248 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cantisym) A) p0003 p0247
  have p0249 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wbr R (syn_cantisym) A) syntaxFormula0035 p0248
  have p0250 := @g_brex R A (syn_cantisym)
  have p0251 := @g_breq (.cv a) (.cv b) (.cv r) R
  have p0252 := @g_breq (.cv b) (.cv a) (.cv r) R
  have p0253 :=
    @g_anbi12d (.classEq (.cv r) R) (syn_wbr (.cv a) (.cv r) (.cv b))
      (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) (.cv r) (.cv a))
      (syn_wbr (.cv b) R (.cv a)) p0251 p0252
  have p0254 :=
    @g_imbi1d (.classEq (.cv r) R)
      (syn_wa (syn_wbr (.cv a) (.cv r) (.cv b)) (syn_wbr (.cv b) (.cv r) (.cv a)))
      (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a))) (.objEq a b) p0253
  have p0255 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (.imp (syn_wa (syn_wbr (.cv a) (.cv r) (.cv b)) (syn_wbr (.cv b) (.cv r) (.cv a)))
        (.objEq a b))
      (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a))) (.objEq a b))
      a b (.cv c) (.cv c) dv_cache_0064 dv_cache_0065 p0254
  have p0256 :=
    @g_raleq
      (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a))) (.objEq a b))
      b (.cv c) A dv_cache_0066 dv_cache_0067
  have p0257 :=
    @g_raleqbi1dv
      (syn_wral b (.cv c) (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a)))
          (.objEq a b)))
      (syn_wral b A (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a)))
          (.objEq a b)))
      a (.cv c) A dv_cache_0068 dv_cache_0069 p0256
  have p0258 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_antisym a b r c
      dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
  have p0259 :=
    @g_brabg
      (syn_wral a (.cv c) (syn_wral b (.cv c) (.imp
            (syn_wa (syn_wbr (.cv a) (.cv r) (.cv b)) (syn_wbr (.cv b) (.cv r) (.cv a)))
            (.objEq a b))))
      (syn_wral a (.cv c) (syn_wral b (.cv c)
          (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a))) (.objEq a b))))
      (syn_wral a A (syn_wral b A
          (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a))) (.objEq a b))))
      r c R A (syn_cvv) (syn_cvv) (syn_cantisym) dv_cache_0076 dv_cache_0053 dv_cache_0077
      dv_cache_0048 dv_cache_0078 dv_cache_0079 dv_cache_0080 p0255 p0257 p0258
  have p0260 :=
    @g_syl (syn_wbr R (syn_cantisym) A)
      (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr R (syn_cantisym) A) (syn_wral a A (syn_wral b A
            (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a)))
              (.objEq a b)))))
      p0250 p0259
  have p0261 :=
    @g_ibi (syn_wbr R (syn_cantisym) A)
      (syn_wral a A (syn_wral b A
          (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a))) (.objEq a b))))
      p0260
  have p0262_e01_recanon :
    Nominal.NPrf (.imp (syn_wbr R (syn_cantisym) A) syntaxFormula0041) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wbr, syn_cop, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl,
          syn_wrex, syn_wex, syn_cphi, syn_cantisym, syn_copab, syn_wral]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0261
  have p0262 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      (syn_wbr R (syn_cantisym) A) syntaxFormula0041 p0249 p0262_e01_recanon
  have p0263 :=
    @g_simpl (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0264 :=
    @g_elfpiv A (.cv x) (.cv y) R e c dv_cache_0040 dv_cache_0041 dv_cache_0002
      dv_cache_0048 dv_cache_0027 dv_cache_0044 dv_cache_0045 dv_cache_0049 dv_cache_0050
      dv_cache_0046 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0033 dv_cache_0054
  have p0265 :=
    @g_biimpi (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0034 p0264
  have p0266 :=
    @g_simpll (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 (.cv x) (.cv y)))
      syntaxFormula0033
  have p0267 :=
    @g_syl (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0034
      (.classMem (.cv e) A) p0265 p0266
  have p0268 :=
    @g_syl syntaxFormula0035 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) A) p0263 p0267
  have p0269 :=
    @g_simpr (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0270 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0040 dv_cache_0041 dv_cache_0002
      dv_cache_0048 dv_cache_0055 dv_cache_0044 dv_cache_0045 dv_cache_0049 dv_cache_0056
      dv_cache_0046 dv_cache_0051 dv_cache_0057 dv_cache_0053 dv_cache_0058 dv_cache_0059
  have p0271 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0038 p0270
  have p0272 :=
    @g_simpll (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      syntaxFormula0037
  have p0273 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0038
      (.classMem (.cv d) A) p0271 p0272
  have p0274 :=
    @g_syl syntaxFormula0035 (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) A) p0269 p0273
  have p0275 := @g_breq1 (.cv a) (.cv e) (.cv b) R
  have p0276 := @g_breq2 (.cv a) (.cv e) (.cv b) R
  have p0277 :=
    @g_anbi12d (.classEq (.cv a) (.cv e)) (syn_wbr (.cv a) R (.cv b))
      (syn_wbr (.cv e) R (.cv b)) (syn_wbr (.cv b) R (.cv a)) (syn_wbr (.cv b) R (.cv e))
      p0275 p0276
  have p0278 := @g_eqeq1 (.cv a) (.cv e) (.cv b)
  have p0279_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv e)) (syn_wb (.objEq a b) (.classEq (.cv e) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb]
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
      p0278
  have p0279 :=
    @g_imbi12d (.classEq (.cv a) (.cv e))
      (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a)))
      (syn_wa (syn_wbr (.cv e) R (.cv b)) (syn_wbr (.cv b) R (.cv e))) (.objEq a b)
      (.classEq (.cv e) (.cv b)) p0277 p0279_e01_recanon
  have p0280 := @g_breq2 (.cv b) (.cv d) (.cv e) R
  have p0281 := @g_breq1 (.cv b) (.cv d) (.cv e) R
  have p0282 :=
    @g_anbi12d (.classEq (.cv b) (.cv d)) (syn_wbr (.cv e) R (.cv b))
      (syn_wbr (.cv e) R (.cv d)) (syn_wbr (.cv b) R (.cv e)) (syn_wbr (.cv d) R (.cv e))
      p0280 p0281
  have p0283 := @g_eqeq2 (.cv b) (.cv d) (.cv e)
  have p0284 :=
    @g_imbi12d (.classEq (.cv b) (.cv d))
      (syn_wa (syn_wbr (.cv e) R (.cv b)) (syn_wbr (.cv b) R (.cv e)))
      (syn_wa (syn_wbr (.cv e) R (.cv d)) (syn_wbr (.cv d) R (.cv e)))
      (.classEq (.cv e) (.cv b)) (.classEq (.cv e) (.cv d)) p0282 p0283
  have p0285 :=
    @g_rspc2v
      (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a))) (.objEq a b))
      syntaxFormula0042
      (.imp (syn_wa (syn_wbr (.cv e) R (.cv b)) (syn_wbr (.cv b) R (.cv e)))
        (.classEq (.cv e) (.cv b)))
      a b (.cv e) (.cv d) A A dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0069
      dv_cache_0069 dv_cache_0067 dv_cache_0084 dv_cache_0085 dv_cache_0075 p0279 p0284
  have p0286 :=
    @g_syl2anc syntaxFormula0035 (.classMem (.cv e) A) (.classMem (.cv d) A)
      (.imp (syn_wral a A (syn_wral b A
            (.imp (syn_wa (syn_wbr (.cv a) R (.cv b)) (syn_wbr (.cv b) R (.cv a)))
              (.objEq a b)))) syntaxFormula0042)
      p0268 p0274 p0285
  have p0287_e01_recanon :
    Nominal.NPrf (.imp syntaxFormula0035 (.imp syntaxFormula0041 syntaxFormula0042)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_wral]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0286
  have p0287 :=
    @g_sylcom (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      syntaxFormula0041 syntaxFormula0042 p0262 p0287_e01_recanon
  have p0288 :=
    @g_syl7bi (syn_wa (syn_wbr (.cv d) R (.cv e)) (syn_wbr (.cv e) R (.cv d)))
      (syn_wa (syn_wbr (.cv e) R (.cv d)) (syn_wbr (.cv d) R (.cv e)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      (.classEq (.cv e) (.cv d)) p0246 p0287
  have p0289 :=
    @g_exp4a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      (syn_wbr (.cv d) R (.cv e)) (syn_wbr (.cv e) R (.cv d)) (.classEq (.cv e) (.cv d))
      p0288
  have p0290 :=
    Nominal.ax2 (syn_wbr (.cv d) R (.cv e)) (syn_wbr (.cv e) R (.cv d))
      (.classEq (.cv e) (.cv d))
  have p0291 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      (.imp (syn_wbr (.cv d) R (.cv e))
        (.imp (syn_wbr (.cv e) R (.cv d)) (.classEq (.cv e) (.cv d))))
      (.imp (.imp (syn_wbr (.cv d) R (.cv e)) (syn_wbr (.cv e) R (.cv d)))
        (.imp (syn_wbr (.cv d) R (.cv e)) (.classEq (.cv e) (.cv d))))
      p0289 p0290
  have p0292 :=
    @g_mpdi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      (.imp (syn_wbr (.cv d) R (.cv e)) (syn_wbr (.cv e) R (.cv d)))
      (.imp (syn_wbr (.cv d) R (.cv e)) (.classEq (.cv e) (.cv d))) p0245 p0291
  have p0293 :=
    @g_mpdi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      (syn_wbr (.cv d) R (.cv e)) (.classEq (.cv e) (.cv d)) p0217 p0292
  have p0294 := @g_eqcom (.cv e) (.cv d)
  have p0295 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      (.classEq (.cv e) (.cv d)) (.classEq (.cv d) (.cv e)) p0293 p0294
  have p0297 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_csn (.cv e))) (.classEq (.cv d) (.cv e)))
      syntaxFormula0035 p0184
  have p0298 :=
    @g_biimprd syntaxFormula0035 (.classMem (.cv d) (syn_csn (.cv e)))
      (.classEq (.cv d) (.cv e)) p0297
  have p0299 :=
    @g_sylcom (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0035
      (.classEq (.cv d) (.cv e)) (.classMem (.cv d) (syn_csn (.cv e))) p0295 p0298
  have p0300 :=
    @g_exp3a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csn (.cv e))) p0299
  have p0301 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.imp (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
        (.imp (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
          (.classMem (.cv d) (syn_csn (.cv e)))))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) p0300
  have p0302 :=
    @g_bi3 (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csn (.cv e)))
  have p0303 :=
    @g_syl8 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.imp (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
        (.classMem (.cv d) (syn_csn (.cv e))))
      syntaxFormula0044 p0301 p0302
  have p0304 :=
    Nominal.ax2 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0031
      syntaxFormula0043
  have p0305 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.imp (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0044)
      (.imp (.imp (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0031)
        (.imp (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0043))
      p0303 p0304
  have p0306 :=
    @g_mpdi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.imp (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0031)
      (.imp (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0043) p0190
      p0305
  have p0307 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0043 p0306
  have p0308 :=
    @g_alrimdv (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) syntaxFormula0043 d
      dv_cache_0086 dv_cache_0087 p0307
  have p0309 :=
    @g_dfcleq d (syn_cfpiv R A (.cv x) (.cv y)) (syn_csn (.cv e)) dv_cache_0088
      dv_cache_0089
  have p0310 :=
    @g_syl6ibr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) (.all d syntaxFormula0043)
      (.classEq (syn_cfpiv R A (.cv x) (.cv y)) (syn_csn (.cv e))) p0308 p0309
  have p0311 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.imp (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
        (.classEq (syn_cfpiv R A (.cv x) (.cv y)) (syn_csn (.cv e))))
      syntaxFormula0028 p0310
  have p0312 :=
    @g_mpdi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classEq (syn_cfpiv R A (.cv x) (.cv y)) (syn_csn (.cv e))) p0181 p0311
  have p0313 := @g_eqcom (syn_cfpiv R A (.cv x) (.cv y)) (syn_csn (.cv e))
  have p0314 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (.classEq (syn_cfpiv R A (.cv x) (.cv y)) (syn_csn (.cv e)))
      (.classEq (syn_csn (.cv e)) (syn_cfpiv R A (.cv x) (.cv y))) p0312 p0313
  have p0315 := @g_eqeq2 (syn_csn (.cv e)) (syn_cfpiv R A (.cv x) (.cv y)) (.cv q)
  have p0316 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (.classEq (syn_csn (.cv e)) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wb (.classEq (.cv q) (syn_csn (.cv e)))
        (.classEq (.cv q) (syn_cfpiv R A (.cv x) (.cv y))))
      p0314 p0315
  have p0317 :=
    @g_bi1 (.classEq (.cv q) (syn_csn (.cv e)))
      (.classEq (.cv q) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0318 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (syn_wb (.classEq (.cv q) (syn_csn (.cv e)))
        (.classEq (.cv q) (syn_cfpiv R A (.cv x) (.cv y))))
      (.imp (.classEq (.cv q) (syn_csn (.cv e)))
        (.classEq (.cv q) (syn_cfpiv R A (.cv x) (.cv y))))
      p0316 p0317
  have p0319 :=
    @g_mpdi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (.classEq (.cv q) (syn_csn (.cv e)))
      (.classEq (.cv q) (syn_cfpiv R A (.cv x) (.cv y))) p0180 p0318
  have p0320 := @g_eleq1 (.cv q) (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X)
  have p0321 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (.classEq (.cv q) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wb (.classMem (.cv q) (syn_cfdpivrange2 R A X))
        (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X)))
      p0319 p0320
  have p0322 :=
    @g_bicom (.classMem (.cv q) (syn_cfdpivrange2 R A X))
      (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
  have p0323 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (syn_wb (.classMem (.cv q) (syn_cfdpivrange2 R A X))
        (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X)))
      (syn_wb (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
        (.classMem (.cv q) (syn_cfdpivrange2 R A X)))
      p0321 p0322
  have p0324 :=
    @g_bi1 (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X))
  have p0325 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (syn_wb (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
        (.classMem (.cv q) (syn_cfdpivrange2 R A X)))
      (.imp (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
        (.classMem (.cv q) (syn_cfdpivrange2 R A X)))
      p0323 p0324
  have p0326 := @g_id (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
  have p0327 :=
    @g_a1ii
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (.imp syntaxFormula0028
          (.imp (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
            (.classMem (.cv q) (syn_cfdpivrange2 R A X)))))
      (.imp (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
        (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X)))
      p0325 p0326
  have p0328 :=
    @g_mpdd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0028
      (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A X))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X)) p0175 p0327
  have p0329 :=
    @g_exp3a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0027
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X)) p0328
  have p0330 :=
    @g_exp3a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0024
      (syn_wa (.classMem (.cv x) X) (.classMem (.cv y) X)) syntaxFormula0045 p0329
  have p0331 :=
    @g_exp4a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0024
      (.classMem (.cv x) X) (.classMem (.cv y) X) syntaxFormula0045 p0330
  have p0332 :=
    @g_imp3a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0024
      (.classMem (.cv x) X) syntaxFormula0046 p0331
  have p0333 :=
    @g_alimdv (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0026
      syntaxFormula0046 y dv_cache_0090 p0332
  have p0334 :=
    @g_syl5 syntaxFormula0026 (.all y syntaxFormula0026)
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (.all y syntaxFormula0046)
      p0157 p0333
  have p0335 := (Nominal.biimpRefl syntaxFormula0047)
  have p0336 :=
    @g_syl6ibr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0026
      (.all y syntaxFormula0046) syntaxFormula0047 p0334 p0335
  have p0337 := @g_nfv (.classMem (.cv q) (syn_cfdpivrange2 R A X)) y dv_cache_0091
  have p0338 :=
    @g_r19_23 (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X)) y X p0337
  have p0339 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0026
      syntaxFormula0047 syntaxFormula0048 p0336 p0338
  have p0340 :=
    @g_exp3a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0024
      (.classMem (.cv x) X) syntaxFormula0048 p0339
  have p0341 :=
    @g_alimdv (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0024
      syntaxFormula0049 x dv_cache_0092 p0340
  have p0342 :=
    @g_syl5 syntaxFormula0024 (.all x syntaxFormula0024)
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (.all x syntaxFormula0049)
      p0155 p0341
  have p0343 := (Nominal.biimpRefl syntaxFormula0050)
  have p0344 :=
    @g_syl6ibr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0024
      (.all x syntaxFormula0049) syntaxFormula0050 p0342 p0343
  have p0345 := @g_nfv (.classMem (.cv q) (syn_cfdpivrange2 R A X)) x dv_cache_0093
  have p0346 :=
    @g_r19_23 (syn_wrex y X (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X)) x X p0345
  have p0347 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0024
      syntaxFormula0050
      (.imp syntaxFormula0025 (.classMem (.cv q) (syn_cfdpivrange2 R A X))) p0344 p0346
  have p0348 :=
    @g_mpdi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0024
      syntaxFormula0025 (.classMem (.cv q) (syn_cfdpivrange2 R A X)) p0153 p0347
  have p0349 :=
    @g_exp3a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0023
      (.classEq (.cv q) (syn_csn (.cv e))) (.classMem (.cv q) (syn_cfdpivrange2 R A X))
      p0348
  have p0350 :=
    @g_exp3a (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))
      (.classMem (.cv e) (syn_cfdif R A X)) syntaxFormula0051 p0349
  have p0351 :=
    @g_alimdv (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X))) syntaxFormula0052 e dv_cache_0094
      p0350
  have p0352 :=
    @g_syl5 (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))
      (.all e (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (.all e syntaxFormula0052)
      p0145 p0351
  have p0353 := (Nominal.biimpRefl syntaxFormula0053)
  have p0354 :=
    @g_syl6ibr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X))) (.all e syntaxFormula0052)
      syntaxFormula0053 p0352 p0353
  have p0355 := @g_nfv (.classMem (.cv q) (syn_cfdpivrange2 R A X)) e dv_cache_0095
  have p0356 :=
    @g_r19_23 (.classEq (.cv q) (syn_csn (.cv e)))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X)) e (syn_cfdif R A X) p0355
  have p0357 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X))) syntaxFormula0053
      (.imp (syn_wrex e (syn_cfdif R A X) (.classEq (.cv q) (syn_csn (.cv e))))
        (.classMem (.cv q) (syn_cfdpivrange2 R A X)))
      p0354 p0356
  have p0358 :=
    @g_mpdi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (.cv q) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wrex e (syn_cfdif R A X) (.classEq (.cv q) (syn_csn (.cv e))))
      (.classMem (.cv q) (syn_cfdpivrange2 R A X)) p0143 p0357
  have p0359 :=
    @g_ssrdv (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) q
      (syn_cpw1 (syn_cfdif R A X)) (syn_cfdpivrange2 R A X) dv_cache_0096 dv_cache_0097
      dv_cache_0098 p0358
  have p0360 :=
    @g_fdpivrange2ex A X R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0361 := @g_ncid (syn_cfdpivrange2 R A X) p0360
  have p0362 := @g_id syntaxFormula0054
  have p0363 := @g_pw1exg (syn_cfdif R A X) (syn_cvv)
  have p0364 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cfdif R A X) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cvv)) p0009 p0363
  have p0365 := @g_ncidg (syn_cpw1 (syn_cfdif R A X)) (syn_cvv)
  have p0366 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      p0364 p0365
  have p0367 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      syntaxFormula0054 p0366
  have p0368 := @g_sseq1 (.cv x) (syn_cpw1 (syn_cfdif R A X)) (.cv y)
  have p0369 := @g_sseq2 (.cv y) (syn_cfdpivrange2 R A X) (syn_cpw1 (syn_cfdif R A X))
  have p0370 :=
    @g_rspc2ev (syn_wss (.cv x) (.cv y))
      (syn_wss (syn_cpw1 (syn_cfdif R A X)) (syn_cfdpivrange2 R A X))
      (syn_wss (syn_cpw1 (syn_cfdif R A X)) (.cv y)) x y (syn_cpw1 (syn_cfdif R A X))
      (syn_cfdpivrange2 R A X) (syn_cnc (syn_cpw1 (syn_cfdif R A X)))
      (syn_cnc (syn_cfdpivrange2 R A X)) dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0008
      p0368 p0369
  have p0371 :=
    @g_n_3expb
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      (.classMem (syn_cfdpivrange2 R A X) (syn_cnc (syn_cfdpivrange2 R A X)))
      (syn_wss (syn_cpw1 (syn_cfdif R A X)) (syn_cfdpivrange2 R A X)) syntaxFormula0055
      p0370
  have p0372 :=
    @g_ex (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      syntaxFormula0054 syntaxFormula0055 p0371
  have p0373 :=
    @g_syl56 syntaxFormula0054 syntaxFormula0054
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      (.imp syntaxFormula0054 syntaxFormula0055) p0362 p0367 p0372
  have p0374 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0054
      syntaxFormula0055 p0373
  have p0375 :=
    @g_mpani (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cfdpivrange2 R A X) (syn_cnc (syn_cfdpivrange2 R A X)))
      (syn_wss (syn_cpw1 (syn_cfdif R A X)) (syn_cfdpivrange2 R A X)) syntaxFormula0055
      p0361 p0374
  have p0376 := @g_ncex (syn_cpw1 (syn_cfdif R A X))
  have p0377 := @g_ncex (syn_cfdpivrange2 R A X)
  have p0378 :=
    @g_brlec x y (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cnc (syn_cfdpivrange2 R A X))
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0008 p0376 p0377
  have p0379 :=
    @g_syl6ibr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wss (syn_cpw1 (syn_cfdif R A X)) (syn_cfdpivrange2 R A X)) syntaxFormula0055
      syntaxFormula0056 p0375 p0378
  have p0380 :=
    @g_mpd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wss (syn_cpw1 (syn_cfdif R A X)) (syn_cfdpivrange2 R A X)) syntaxFormula0056
      p0359 p0379
  have p0381 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0056
      (syn_wwpp) p0380
  have p0382 :=
    @g_wppfdpivrangencdlitraw A X R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0383 := @g_pm3_2 syntaxFormula0056 syntaxFormula0057
  have p0384 :=
    @g_syl5 (syn_wwpp) syntaxFormula0057 syntaxFormula0056 syntaxFormula0058 p0382 p0383
  have p0385 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0056 (.imp (syn_wwpp) syntaxFormula0058) p0381 p0384
  have p0386 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0058 p0385
  have p0388 := @g_ncelncs (syn_cfdpivrange2 R A X) (syn_cvv)
  have p0389 := Nominal.mp p0360 p0388
  have p0390 := @g_xpkex X X hyp_cfbfdwppcarrierimpndv_3 hyp_cfbfdwppcarrierimpndv_3
  have p0391 := @g_nncex
  have p0392 := @g_xpex (syn_cxpk X X) (syn_cnnc) p0390 p0391
  have p0393 := @g_ncelncs (syn_cxp (syn_cxpk X X) (syn_cnnc)) (syn_cvv)
  have p0394 := Nominal.mp p0392 p0393
  have p0395 := @g_ncelncs (syn_cpw1 (syn_cfdif R A X)) (syn_cvv)
  have p0396 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cvv))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs)) p0364 p0395
  have p0397 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs)) syntaxFormula0059
      p0396
  have p0398 := Nominal.ax1 syntaxFormula0059 syntaxFormula0059
  have p0399 := Nominal.ax1 syntaxFormula0059 syntaxFormula0060
  have p0400 := @g_mpd syntaxFormula0059 syntaxFormula0060 syntaxFormula0059 p0398 p0399
  have p0401 :=
    @g_a1i syntaxFormula0060 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      p0400
  have p0402 :=
    @g_lectr (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cnc (syn_cfdpivrange2 R A X))
      (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))
  have p0403 :=
    @g_n_3expb (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs))
      (.classMem (syn_cnc (syn_cfdpivrange2 R A X)) (syn_cncs))
      (.classMem (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs))
      syntaxFormula0062 p0402
  have p0404 :=
    @g_ex (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs)) syntaxFormula0059
      syntaxFormula0062 p0403
  have p0405 :=
    @g_syl6c (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0059
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs)) syntaxFormula0059
      syntaxFormula0062 p0397 p0401 p0404
  have p0406 :=
    @g_mp2ani (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cfdpivrange2 R A X)) (syn_cncs))
      (.classMem (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs))
      syntaxFormula0062 p0389 p0394 p0405
  have p0407 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0058 syntaxFormula0061 p0386 p0406
  have p0413 :=
    @g_jctir (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs))
      (.classMem (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs)) p0396 p0394
  have p0414 :=
    @g_tlecg (syn_cnc (syn_cpw1 (syn_cfdif R A X)))
      (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))
  have p0415 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs))
        (.classMem (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs)))
      (syn_wb syntaxFormula0061 syntaxFormula0063) p0413 p0414
  have p0416 :=
    @g_sylibd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0061 syntaxFormula0063 p0407 p0415
  have p0417 := @g_tccl (syn_cnc (syn_cpw1 (syn_cfdif R A X)))
  have p0418 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs))
      (.classMem (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_cncs)) p0396 p0417
  have p0424 := @g_tccl (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))
  have p0425 := Nominal.mp p0394 p0424
  have p0426 :=
    @g_jctir (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_cncs))
      (.classMem (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))) (syn_cncs)) p0418
      p0425
  have p0427 :=
    @g_tlecg (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))))
  have p0428 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa (.classMem (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_cncs))
        (.classMem (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))) (syn_cncs)))
      (syn_wb syntaxFormula0063 syntaxFormula0064) p0426 p0427
  have p0429 :=
    @g_sylibd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0063 syntaxFormula0064 p0416 p0428
  have p0430 :=
    @g_fdordwe2 A X R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0431 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wbr R (syn_cwe) A) (syn_wbr (syn_cfdord R A X) (syn_cwe) (syn_cfdif R A X))
      p0003 p0430
  have p0432 := @g_siwendv (syn_cfdif R A X) (syn_cfdord R A X)
  have p0433 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wbr (syn_cfdord R A X) (syn_cwe) (syn_cfdif R A X))
      (syn_wbr (syn_csi (syn_cfdord R A X)) (syn_cwe) (syn_cpw1 (syn_cfdif R A X))) p0431
      p0432
  have p0434 :=
    @g_ncwehwcardsndv (syn_cpw1 (syn_cfdif R A X)) (syn_csi (syn_cfdord R A X))
  have p0435 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wbr (syn_csi (syn_cfdord R A X)) (syn_cwe) (syn_cpw1 (syn_cfdif R A X)))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_chwcards (syn_cvv))) p0433
      p0434
  have p0436 := @g_hwcardstcclndv (syn_cnc (syn_cpw1 (syn_cfdif R A X)))
  have p0437 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_chwcards (syn_cvv)))
      p0435 p0436
  have p0438 := @g_hwcardstcclndv (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
  have p0439 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_chwcards (syn_cvv)))
      syntaxFormula0065 p0437 p0438
  have p0443 := @g_hncardhwcardsndv (syn_cxp (syn_cxpk X X) (syn_cnnc))
  have p0444 := Nominal.mp p0392 p0443
  have p0445 :=
    @g_jctir (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0065
      (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_chwcards (syn_cvv)))
      p0439 p0444
  have p0446 :=
    @g_hwcardslecconnexndv (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))))
      (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc)))
  have p0447 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa syntaxFormula0065 (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc)))
          (syn_chwcards (syn_cvv))))
      syntaxFormula0068 p0445 p0446
  have p0448 := @g_pm2_53 syntaxFormula0066 syntaxFormula0067
  have p0449 := @g_hncardtc2nodomndv (syn_cxp (syn_cxpk X X) (syn_cnnc)) p0392
  have p0450 := @g_notnot2 syntaxFormula0067
  have p0455 := @g_tccl (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))))
  have p0456 := Nominal.mp p0425 p0455
  have p0457 := @g_hwcardssnc (syn_cvv)
  have p0458 :=
    @g_sseldi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_chwcards (syn_cvv)) (syn_cncs)
      (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X))))) p0457 p0439
  have p0459 := @g_hncardnc (syn_cxp (syn_cxpk X X) (syn_cnnc))
  have p0460 := Nominal.mp p0392 p0459
  have p0461 :=
    @g_jctil (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0069
      (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs)) p0458 p0460
  have p0462 :=
    @g_biantrurd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs))
        syntaxFormula0069)
      syntaxFormula0070 p0461
  have p0463 := (Nominal.biimpRefl syntaxFormula0071)
  have p0464 :=
    @g_syl6rbbr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0070
      (syn_wa (syn_wa (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs))
          syntaxFormula0069) syntaxFormula0070)
      syntaxFormula0071 p0462 p0463
  have p0465 :=
    @g_mpbiri (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0071
      syntaxFormula0070 p0456 p0464
  have p0466 :=
    @g_lectr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc)))
      (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))))
      (syn_ctc (syn_ctc (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))))
  have p0467 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0071
      (.imp (syn_wa syntaxFormula0067 syntaxFormula0064) syntaxFormula0072) p0465 p0466
  have p0468 :=
    @g_exp3acom23 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      syntaxFormula0067 syntaxFormula0064 syntaxFormula0072 p0467
  have p0469 :=
    @g_syl7 syntaxFormula0074 syntaxFormula0067
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0064
      syntaxFormula0072 p0450 p0468
  have p0470 := @g_notnot1 syntaxFormula0072
  have p0471 :=
    @g_syl8 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0064
      syntaxFormula0074 syntaxFormula0072 (.neg syntaxFormula0075) p0469 p0470
  have p0472 := Nominal.ax3 syntaxFormula0073 syntaxFormula0075
  have p0473 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0064
      (.imp syntaxFormula0074 (.neg syntaxFormula0075))
      (.imp syntaxFormula0075 syntaxFormula0073) p0471 p0472
  have p0474 :=
    @g_mpii (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0064
      syntaxFormula0075 syntaxFormula0073 p0449 p0473
  have p0475 :=
    @g_a1dd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0064
      syntaxFormula0073 syntaxFormula0076 p0474
  have p0476 := Nominal.ax3 syntaxFormula0066 syntaxFormula0067
  have p0477 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0064
      (.imp syntaxFormula0076 syntaxFormula0073)
      (.imp syntaxFormula0067 syntaxFormula0066) p0475 p0476
  have p0478 :=
    @g_com23 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0064
      syntaxFormula0067 syntaxFormula0066 p0477
  have p0479 :=
    @g_syl9r syntaxFormula0068 syntaxFormula0076 syntaxFormula0067
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0077 p0448
      p0478
  have p0480 := @g_notnot1 syntaxFormula0077
  have p0481 :=
    @g_syl8 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0068
      syntaxFormula0076 syntaxFormula0077 syntaxFormula0079 p0479 p0480
  have p0482 := Nominal.ax3 syntaxFormula0066 syntaxFormula0078
  have p0483 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0068
      (.imp syntaxFormula0076 syntaxFormula0079) syntaxFormula0080 p0481 p0482
  have p0484 := @g_idd syntaxFormula0064 syntaxFormula0066
  have p0485 := @g_com12 syntaxFormula0064 syntaxFormula0066 syntaxFormula0066 p0484
  have p0486 := @g_a1i syntaxFormula0081 syntaxFormula0068 p0485
  have p0487 := @g_a1d syntaxFormula0068 syntaxFormula0081 syntaxFormula0078 p0486
  have p0488 :=
    @g_a2d syntaxFormula0068 syntaxFormula0078 syntaxFormula0066 syntaxFormula0077 p0487
  have p0489 :=
    @g_sylcom (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0068
      syntaxFormula0080 syntaxFormula0082 p0483 p0488
  have p0490 := @g_pm2_18 syntaxFormula0077
  have p0491 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0068
      syntaxFormula0082 syntaxFormula0077 p0489 p0490
  have p0492 :=
    @g_com23 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0068
      syntaxFormula0064 syntaxFormula0066 p0491
  have p0493 :=
    @g_mpid (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0064
      syntaxFormula0068 syntaxFormula0066 p0447 p0492
  have p0494 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0064 syntaxFormula0066 p0429 p0493
  have p0495 := @g_a1i syntaxFormula0083 (syn_wwpp) hyp_cfbfdwppcarrierimpndv_4
  have p0496 := @g_pm3_2 syntaxFormula0066 syntaxFormula0083
  have p0497 :=
    @g_syl5 (syn_wwpp) syntaxFormula0083 syntaxFormula0066 syntaxFormula0084 p0495 p0496
  have p0498 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0066 (.imp (syn_wwpp) syntaxFormula0084) p0494 p0497
  have p0499 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0084 p0498
  have p0505 := @g_hncardnc X
  have p0506 := Nominal.mp hyp_cfbfdwppcarrierimpndv_3 p0505
  have p0507 := @g_tccl (syn_chncard X)
  have p0508 := Nominal.mp p0506 p0507
  have p0509 := @g_tccl (syn_ctc (syn_chncard X))
  have p0510 := Nominal.mp p0508 p0509
  have p0511 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0069
      syntaxFormula0085 p0458
  have p0512 := Nominal.ax1 syntaxFormula0085 syntaxFormula0085
  have p0513 := Nominal.ax1 syntaxFormula0085 syntaxFormula0086
  have p0514 := @g_mpd syntaxFormula0085 syntaxFormula0086 syntaxFormula0085 p0512 p0513
  have p0515 :=
    @g_a1i syntaxFormula0086 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      p0514
  have p0516 :=
    @g_lectr (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))))
      (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc)))
      (syn_ctc (syn_ctc (syn_chncard X)))
  have p0517 :=
    @g_n_3expb syntaxFormula0069
      (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_chncard X))) (syn_cncs)) syntaxFormula0088 p0516
  have p0518 := @g_ex syntaxFormula0069 syntaxFormula0085 syntaxFormula0088 p0517
  have p0519 :=
    @g_syl6c (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0085
      syntaxFormula0069 syntaxFormula0085 syntaxFormula0088 p0511 p0515 p0518
  have p0520 :=
    @g_mp2ani (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_chncard X))) (syn_cncs)) syntaxFormula0088 p0460
      p0510 p0519
  have p0521 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0084 syntaxFormula0087 p0499 p0520
  have p0526 :=
    @g_jctir (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_cncs))
      (.classMem (syn_ctc (syn_chncard X)) (syn_cncs)) p0418 p0508
  have p0527 :=
    @g_tlecg (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_ctc (syn_chncard X))
  have p0528 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa (.classMem (syn_ctc (syn_cnc (syn_cpw1 (syn_cfdif R A X)))) (syn_cncs))
        (.classMem (syn_ctc (syn_chncard X)) (syn_cncs)))
      (syn_wb syntaxFormula0089 syntaxFormula0087) p0526 p0527
  have p0529 :=
    @g_sylibrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0087 syntaxFormula0089 p0521 p0528
  have p0532 :=
    @g_jctir (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs))
      (.classMem (syn_chncard X) (syn_cncs)) p0396 p0506
  have p0533 := @g_tlecg (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_chncard X)
  have p0534 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wa (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs))
        (.classMem (syn_chncard X) (syn_cncs)))
      (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_clec) (syn_chncard X))
        syntaxFormula0089)
      p0532 p0533
  have p0535 :=
    @g_sylibrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0089
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_clec) (syn_chncard X)) p0529
      p0534
  have p0536 := (Nominal.classEqRefl (syn_chncard X))
  have p0537 :=
    @g_breq2i (syn_chncard X) (syn_cnc (syn_chnord X))
      (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_clec) p0536
  have p0538 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_clec) (syn_chncard X))
      syntaxFormula0090 p0535 p0537
  have p0539 := @g_hnordex X hyp_cfbfdwppcarrierimpndv_3
  have p0540 := @g_ncelncsi (syn_chnord X) p0539
  have p0541 :=
    @g_dflec3 g (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cnc (syn_chnord X)) p q
      dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112
  have p0542 :=
    @g_sylancl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs))
      (.classMem (syn_cnc (syn_chnord X)) (syn_cncs))
      (syn_wb syntaxFormula0090 (syn_wrex p (syn_cnc (syn_cpw1 (syn_cfdif R A X)))
          (syn_wrex q (syn_cnc (syn_chnord X)) (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q))))))
      p0396 p0540 p0541
  have p0543 := @g_elnc (.cv p) (syn_cpw1 (syn_cfdif R A X))
  have p0544 := @g_bren (.cv p) (syn_cpw1 (syn_cfdif R A X)) h dv_cache_0113 dv_cache_0114
  have p0545 :=
    @g_bitri (.classMem (.cv p) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      (syn_wbr (.cv p) (syn_cen) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wex h (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))) p0543 p0544
  have p0546 := @g_elnc (.cv q) (syn_chnord X)
  have p0547 := @g_bren (.cv q) (syn_chnord X) i dv_cache_0115 dv_cache_0116
  have p0548 :=
    @g_bitri (.classMem (.cv q) (syn_cnc (syn_chnord X)))
      (syn_wbr (.cv q) (syn_cen) (syn_chnord X))
      (syn_wex i (syn_wf1o (.cv i) (.cv q) (syn_chnord X))) p0546 p0547
  have p0549 :=
    @g_anbi12i (.classMem (.cv p) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      (syn_wex h (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X))))
      (.classMem (.cv q) (syn_cnc (syn_chnord X)))
      (syn_wex i (syn_wf1o (.cv i) (.cv q) (syn_chnord X))) p0545 p0548
  have p0550 :=
    @g_eeanv (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1o (.cv i) (.cv q) (syn_chnord X)) h i dv_cache_0117 dv_cache_0118
  have p0551 :=
    @g_bitr4i syntaxFormula0091
      (syn_wa (syn_wex h (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X))))
        (syn_wex i (syn_wf1o (.cv i) (.cv q) (syn_chnord X))))
      (syn_wex h (syn_wex i syntaxFormula0092)) p0549 p0550
  have p0552 := @g_f1of1 (.cv q) (syn_chnord X) (.cv i)
  have p0553 :=
    @g_n_3ad2ant2 (syn_wf1o (.cv i) (.cv q) (syn_chnord X))
      (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1 (.cv i) (.cv q) (syn_chnord X)) (syn_wf1 (.cv g) (.cv p) (.cv q)) p0552
  have p0554 :=
    @g_simp3 (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1o (.cv i) (.cv q) (syn_chnord X)) (syn_wf1 (.cv g) (.cv p) (.cv q))
  have p0555 := @g_f1co (.cv p) (.cv q) (syn_chnord X) (.cv i) (.cv g)
  have p0556 :=
    @g_syl2anc syntaxFormula0093 (syn_wf1 (.cv i) (.cv q) (syn_chnord X))
      (syn_wf1 (.cv g) (.cv p) (.cv q))
      (syn_wf1 (syn_ccom (.cv i) (.cv g)) (.cv p) (syn_chnord X)) p0553 p0554 p0555
  have p0557 := @g_f1ocnv (.cv p) (syn_cpw1 (syn_cfdif R A X)) (.cv h)
  have p0558 := @g_f1of1 (syn_cpw1 (syn_cfdif R A X)) (.cv p) (syn_ccnv (.cv h))
  have p0559 :=
    @g_syl (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1o (syn_ccnv (.cv h)) (syn_cpw1 (syn_cfdif R A X)) (.cv p))
      (syn_wf1 (syn_ccnv (.cv h)) (syn_cpw1 (syn_cfdif R A X)) (.cv p)) p0557 p0558
  have p0560 :=
    @g_n_3ad2ant1 (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1o (.cv i) (.cv q) (syn_chnord X))
      (syn_wf1 (syn_ccnv (.cv h)) (syn_cpw1 (syn_cfdif R A X)) (.cv p))
      (syn_wf1 (.cv g) (.cv p) (.cv q)) p0559
  have p0561 :=
    @g_f1co (syn_cpw1 (syn_cfdif R A X)) (.cv p) (syn_chnord X) (syn_ccom (.cv i) (.cv g))
      (syn_ccnv (.cv h))
  have p0562 :=
    @g_syl2anc syntaxFormula0093
      (syn_wf1 (syn_ccom (.cv i) (.cv g)) (.cv p) (syn_chnord X))
      (syn_wf1 (syn_ccnv (.cv h)) (syn_cpw1 (syn_cfdif R A X)) (.cv p)) syntaxFormula0094
      p0556 p0560 p0561
  have p0563 := @g_vex i
  have p0564 := @g_vex g
  have p0565 := @g_coex (.cv i) (.cv g) p0563 p0564
  have p0566 := @g_vex h
  have p0567 := @g_cnvex (.cv h) p0566
  have p0568 := @g_coex (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)) p0565 p0567
  have p0569 :=
    @g_f1eq1 (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X) (.cv f)
      (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))
  have p0570 :=
    @g_spcev (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))
      syntaxFormula0094 f (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))
      dv_cache_0119 dv_cache_0120 p0568 p0569
  have p0571 :=
    @g_syl syntaxFormula0093 syntaxFormula0094
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))) p0562
      p0570
  have p0572 :=
    @g_n_3expia (syn_wf1o (.cv h) (.cv p) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1o (.cv i) (.cv q) (syn_chnord X)) (syn_wf1 (.cv g) (.cv p) (.cv q))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))) p0571
  have p0573 :=
    @g_exlimivv syntaxFormula0092
      (.imp (syn_wf1 (.cv g) (.cv p) (.cv q))
        (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))))
      h i dv_cache_0121 dv_cache_0122 p0572
  have p0574 :=
    @g_sylbi syntaxFormula0091 (syn_wex h (syn_wex i syntaxFormula0092))
      (.imp (syn_wf1 (.cv g) (.cv p) (.cv q))
        (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))))
      p0551 p0573
  have p0575 :=
    @g_exlimdv syntaxFormula0091 (syn_wf1 (.cv g) (.cv p) (.cv q))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))) g
      dv_cache_0123 dv_cache_0124 p0574
  have p0576 :=
    @g_rexlimivv (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q)))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))) p q
      (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cnc (syn_chnord X)) dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0110 p0575
  have p0577 :=
    @g_syl6bi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0090
      (syn_wrex p (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_wrex q (syn_cnc (syn_chnord X))
          (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q)))))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))) p0542
      p0576
  have p0578 := @g_ncid (syn_chnord X) p0539
  have p0579 := @g_id syntaxFormula0095
  have p0580 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      syntaxFormula0095 p0366
  have p0581 := @g_f1eq2 (.cv a) (syn_cpw1 (syn_cfdif R A X)) (.cv b) (.cv f)
  have p0582 :=
    @g_exbidv (.classEq (.cv a) (syn_cpw1 (syn_cfdif R A X)))
      (syn_wf1 (.cv f) (.cv a) (.cv b))
      (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (.cv b)) f dv_cache_0128 p0581
  have p0583 := @g_f1eq3 (.cv b) (syn_chnord X) (syn_cpw1 (syn_cfdif R A X)) (.cv f)
  have p0584 :=
    @g_exbidv (.classEq (.cv b) (syn_chnord X))
      (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (.cv b))
      (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)) f dv_cache_0129 p0583
  have p0585 :=
    @g_rspc2ev (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (.cv b))) a b
      (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X) (syn_cnc (syn_cpw1 (syn_cfdif R A X)))
      (syn_cnc (syn_chnord X)) dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133
      dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0075 p0582 p0584
  have p0586 :=
    @g_n_3expb
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      (.classMem (syn_chnord X) (syn_cnc (syn_chnord X)))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))
      syntaxFormula0097 p0585
  have p0587 :=
    @g_ex (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      syntaxFormula0095 syntaxFormula0097 p0586
  have p0588 :=
    @g_syl56 syntaxFormula0095 syntaxFormula0095
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cnc (syn_cpw1 (syn_cfdif R A X))))
      (.imp syntaxFormula0095 syntaxFormula0097) p0579 p0580 p0587
  have p0589 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0095
      syntaxFormula0097 p0588
  have p0590 :=
    @g_mpani (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_chnord X) (syn_cnc (syn_chnord X)))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))
      syntaxFormula0097 p0578 p0589
  have p0591 :=
    @g_dflec3 f (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cnc (syn_chnord X)) a b
      dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0075 dv_cache_0138 dv_cache_0139
  have p0592 :=
    @g_sylancl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cnc (syn_cpw1 (syn_cfdif R A X))) (syn_cncs))
      (.classMem (syn_cnc (syn_chnord X)) (syn_cncs))
      (syn_wb syntaxFormula0090 syntaxFormula0097) p0396 p0540 p0591
  have p0593 :=
    @g_sylibrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))
      syntaxFormula0097 syntaxFormula0090 p0590 p0592
  have p0594 :=
    @g_impbid (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0090
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))) p0577
      p0593
  have p0595 :=
    @g_sylibd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0090
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X))) p0538
      p0594
  have p0596 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))
      syntaxFormula0090 p0595 p0593
  have p0597 :=
    @g_f1pw2exim (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X) f h dv_cache_0140
      dv_cache_0114 dv_cache_0141 dv_cache_0142 dv_cache_0143
  have p0598 :=
    @g_syl6 (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0090
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cfdif R A X)) (syn_chnord X)))
      syntaxFormula0099 p0577 p0597
  have p0599 := @g_pwexg (syn_cpw1 (syn_cfdif R A X)) (syn_cvv)
  have p0600 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw1 (syn_cfdif R A X)) (syn_cvv))
      (.classMem (syn_cpw (syn_cpw1 (syn_cfdif R A X))) (syn_cvv)) p0364 p0599
  have p0601 := @g_pwexg (syn_cpw (syn_cpw1 (syn_cfdif R A X))) (syn_cvv)
  have p0602 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw (syn_cpw1 (syn_cfdif R A X))) (syn_cvv))
      (.classMem (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (syn_cvv)) p0600 p0601
  have p0603 := @g_ncelncs (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (syn_cvv)
  have p0604 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (syn_cvv))
      syntaxFormula0100 p0602 p0603
  have p0606 := @g_pwex (syn_chnord X) p0539
  have p0607 := @g_pwex (syn_cpw (syn_chnord X)) p0606
  have p0608 := @g_ncelncsi (syn_cpw (syn_cpw (syn_chnord X))) p0607
  have p0609 :=
    @g_dflec3 g (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) p q dv_cache_0144 dv_cache_0145
      dv_cache_0146 dv_cache_0110 dv_cache_0111 dv_cache_0112
  have p0610 :=
    @g_sylancl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0100
      (.classMem (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cncs))
      (syn_wb syntaxFormula0101 syntaxFormula0102) p0604 p0608 p0609
  have p0611 := @g_elnc (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
  have p0612 :=
    @g_bren (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) a dv_cache_0147
      dv_cache_0148
  have p0613 :=
    @g_bitri
      (.classMem (.cv p) (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
      (syn_wbr (.cv p) (syn_cen) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wex a (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
      p0611 p0612
  have p0614 := @g_elnc (.cv q) (syn_cpw (syn_cpw (syn_chnord X)))
  have p0615 :=
    @g_bren (.cv q) (syn_cpw (syn_cpw (syn_chnord X))) i dv_cache_0115 dv_cache_0149
  have p0616 :=
    @g_bitri (.classMem (.cv q) (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_wbr (.cv q) (syn_cen) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wex i (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))) p0614
      p0615
  have p0617 :=
    @g_anbi12i
      (.classMem (.cv p) (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
      (syn_wex a (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
      (.classMem (.cv q) (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_wex i (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))) p0613
      p0616
  have p0618 :=
    @g_eeanv (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X)))) a i dv_cache_0150
      dv_cache_0151
  have p0619 :=
    @g_bitr4i syntaxFormula0103
      (syn_wa (syn_wex a
          (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))))
        (syn_wex i (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))))
      syntaxFormula0105 p0617 p0618
  have p0620 := @g_f1of1 (.cv q) (syn_cpw (syn_cpw (syn_chnord X))) (.cv i)
  have p0621 :=
    @g_n_3ad2ant2 (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1 (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv g) (.cv p) (.cv q)) p0620
  have p0622 :=
    @g_simp3 (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv g) (.cv p) (.cv q))
  have p0623 := @g_f1co (.cv p) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))) (.cv i) (.cv g)
  have p0624 :=
    @g_syl2anc syntaxFormula0106
      (syn_wf1 (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv g) (.cv p) (.cv q))
      (syn_wf1 (syn_ccom (.cv i) (.cv g)) (.cv p) (syn_cpw (syn_cpw (syn_chnord X))))
      p0621 p0622 p0623
  have p0625 := @g_f1ocnv (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv a)
  have p0626 :=
    @g_f1of1 (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv p) (syn_ccnv (.cv a))
  have p0627 :=
    @g_syl (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1o (syn_ccnv (.cv a)) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv p))
      (syn_wf1 (syn_ccnv (.cv a)) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv p))
      p0625 p0626
  have p0628 :=
    @g_n_3ad2ant1
      (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (syn_ccnv (.cv a)) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv p))
      (syn_wf1 (.cv g) (.cv p) (.cv q)) p0627
  have p0629 :=
    @g_f1co (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv p)
      (syn_cpw (syn_cpw (syn_chnord X))) (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv a))
  have p0630 :=
    @g_syl2anc syntaxFormula0106
      (syn_wf1 (syn_ccom (.cv i) (.cv g)) (.cv p) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (syn_ccnv (.cv a)) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv p))
      syntaxFormula0107 p0624 p0628 p0629
  have p0634 := @g_vex a
  have p0635 := @g_cnvex (.cv a) p0634
  have p0636 := @g_coex (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv a)) p0565 p0635
  have p0637 :=
    @g_f1eq1 (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
      (syn_cpw (syn_cpw (syn_chnord X))) (.cv h)
      (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv a)))
  have p0638 :=
    @g_spcev syntaxFormula0098 syntaxFormula0107 h
      (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv a))) dv_cache_0152 dv_cache_0153
      p0636 p0637
  have p0639 := @g_syl syntaxFormula0106 syntaxFormula0107 syntaxFormula0099 p0630 p0638
  have p0640 :=
    @g_n_3expia
      (syn_wf1o (.cv a) (.cv p) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1o (.cv i) (.cv q) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv g) (.cv p) (.cv q)) syntaxFormula0099 p0639
  have p0641 :=
    @g_exlimivv syntaxFormula0104
      (.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) syntaxFormula0099) a i dv_cache_0154
      dv_cache_0155 p0640
  have p0642 :=
    @g_sylbi syntaxFormula0103 syntaxFormula0105
      (.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) syntaxFormula0099) p0619 p0641
  have p0643 :=
    @g_exlimdv syntaxFormula0103 (syn_wf1 (.cv g) (.cv p) (.cv q)) syntaxFormula0099 g
      dv_cache_0156 dv_cache_0157 p0642
  have p0644 :=
    @g_rexlimivv (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q))) syntaxFormula0099 p q
      (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) dv_cache_0158 dv_cache_0159
      dv_cache_0160 dv_cache_0110 p0643
  have p0645 :=
    @g_syl6bi (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0101
      syntaxFormula0102 syntaxFormula0099 p0610 p0644
  have p0646 := @g_ncid (syn_cpw (syn_cpw (syn_chnord X))) p0607
  have p0647 := @g_id syntaxFormula0109
  have p0648 := @g_ncidg (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (syn_cvv)
  have p0649 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X)))
      (.classMem (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (syn_cvv))
      syntaxFormula0110 p0602 p0648
  have p0650 :=
    @g_a1d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0110
      syntaxFormula0109 p0649
  have p0651 :=
    @g_f1eq2 (.cv b) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv c) (.cv h)
  have p0652 :=
    @g_exbidv (.classEq (.cv b) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_wf1 (.cv h) (.cv b) (.cv c))
      (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv c)) h
      dv_cache_0161 p0651
  have p0653 :=
    @g_f1eq3 (.cv c) (syn_cpw (syn_cpw (syn_chnord X)))
      (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv h)
  have p0654 :=
    @g_exbidv (.classEq (.cv c) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv c))
      syntaxFormula0098 h dv_cache_0162 p0653
  have p0655 :=
    @g_rspc2ev (syn_wex h (syn_wf1 (.cv h) (.cv b) (.cv c))) syntaxFormula0099
      (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))) (.cv c)))
      b c (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X))))
      (syn_cpw (syn_cpw (syn_chnord X)))
      (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) dv_cache_0163 dv_cache_0164
      dv_cache_0165 dv_cache_0166 dv_cache_0167 dv_cache_0168 dv_cache_0169 dv_cache_0170
      dv_cache_0171 p0652 p0654
  have p0656 :=
    @g_n_3expb syntaxFormula0110 syntaxFormula0108 syntaxFormula0099 syntaxFormula0112
      p0655
  have p0657 := @g_ex syntaxFormula0110 syntaxFormula0109 syntaxFormula0112 p0656
  have p0658 :=
    @g_syl56 syntaxFormula0109 syntaxFormula0109
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0110
      (.imp syntaxFormula0109 syntaxFormula0112) p0647 p0650 p0657
  have p0659 :=
    @g_pm2_43d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0109
      syntaxFormula0112 p0658
  have p0660 :=
    @g_mpani (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0108
      syntaxFormula0099 syntaxFormula0112 p0646 p0659
  have p0661 :=
    @g_dflec3 h (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) b c dv_cache_0166 dv_cache_0167
      dv_cache_0168 dv_cache_0171 dv_cache_0172 dv_cache_0173
  have p0662 :=
    @g_sylancl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0100
      (.classMem (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cncs))
      (syn_wb syntaxFormula0101 syntaxFormula0112) p0604 p0608 p0661
  have p0663 :=
    @g_sylibrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0099
      syntaxFormula0112 syntaxFormula0101 p0660 p0662
  have p0664 :=
    @g_impbid (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0101
      syntaxFormula0099 p0645 p0663
  have p0665 :=
    @g_biimprd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0101
      syntaxFormula0099 p0664
  have p0666 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0090
      syntaxFormula0099 syntaxFormula0101 p0598 p0665
  have p0667 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0090 syntaxFormula0101 p0596 p0666
  have p0668 :=
    @g_jcad (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0022 syntaxFormula0101 p0141 p0667
  have p0672 := @g_ncelncs (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv)
  have p0673 := Nominal.mp p0607 p0672
  have p0680 := @g_tccl (syn_ctc (syn_ctc (syn_cnc A)))
  have p0681 := Nominal.mp p0021 p0680
  have p0682 :=
    @g_lectr (syn_ctc (syn_ctc (syn_ctc (syn_cnc A))))
      (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 (syn_cfdif R A X)))))
      (syn_cnc (syn_cpw (syn_cpw (syn_chnord X))))
  have p0683 :=
    @g_mp3an1 (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_cnc A)))) (syn_cncs))
      syntaxFormula0100
      (.classMem (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cncs))
      syntaxFormula0115 p0681 p0682
  have p0684 :=
    @g_sylancl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) syntaxFormula0100
      (.classMem (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cncs))
      syntaxFormula0115 p0604 p0673 p0683
  have p0685 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0113 syntaxFormula0114 p0668 p0684
  have p0686 := @g_tc3nc A hyp_cfbfdwppcarrierimpndv_2
  have p0687 :=
    @g_breq1i (syn_ctc (syn_ctc (syn_ctc (syn_cnc A))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 A))))
      (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))) (syn_clec) p0686
  have p0688 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      syntaxFormula0114
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 A)))) (syn_clec)
        (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))))
      p0685 p0687
  have p0689 := @g_pw1ex A hyp_cfbfdwppcarrierimpndv_2
  have p0690 := @g_pw1ex (syn_cpw1 A) p0689
  have p0691 := @g_pw1ex (syn_cpw1 (syn_cpw1 A)) p0690
  have p0695 :=
    @g_nclenc (syn_cpw1 (syn_cpw1 (syn_cpw1 A))) (syn_cpw (syn_cpw (syn_chnord X))) k
      dv_cache_0174 dv_cache_0175 p0691 p0607
  have p0696 :=
    @g_syl6ib (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw X))) (syn_wwpp)
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 A)))) (syn_clec)
        (syn_cnc (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 A)))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      p0688 p0695
  exact p0696


end NFChoice.DirectNominalPrf.WPPReplay
