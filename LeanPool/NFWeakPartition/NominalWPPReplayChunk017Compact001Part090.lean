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

/-- Checked nominal proof certificate identified upstream as `g_cfbfdwppcarrierimpndv`. -/
@[expose]
noncomputable def gCfbfdwppcarrierimpndv (A : Class) (R : Class) (k : Var) (X : Class)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_X : Disjoint A.fv X.fv) (dv_A_k : k ∉ A.fv)
    (dv_R_X : Disjoint R.fv X.fv) (_dv_R_k : k ∉ R.fv) (dv_X_k : k ∉ X.fv)
    (hyp_cfbfdwppcarrierimpndv_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_cfbfdwppcarrierimpndv_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_cfbfdwppcarrierimpndv_3 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbfdwppcarrierimpndv_4 : Nominal.NPrf
        (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
          (synCtc (synCtc (synChncard X))))) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (.imp (synWwpp) (synWex k
            (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 A)))
              (synCpw (synCpw (synChnord X))))))) :=
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
  have dv_cache_0004 : x ∉ ((synCpw1fn)).fv :=
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
  have dv_cache_0005 : y ∉ ((synCpw1fn)).fv :=
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
  have dv_cache_0006 : x ∉ ((synCpw1 (synCpw (synCpw (synCfdif R A X))))).fv :=
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
  have dv_cache_0007 : y ∉ ((synCpw1 (synCpw (synCpw (synCfdif R A X))))).fv :=
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
  have dv_cache_0010 : z ∉ ((synCpw (synCfdif R A X))).fv :=
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
  have dv_cache_0012 : z ∉ ((synCpw (synCpw (synCfdif R A X)))).fv :=
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
  have dv_cache_0013 : z ∉ ((synWbr (.cv y) (synCpw1fn) (.cv x))).fv :=
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
  have dv_cache_0014 : y ∉ ((synCpw (synCpw (synCfdif R A X)))).fv :=
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
  have dv_cache_0016 : y ∉ ((synCsn (.cv z))).fv :=
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
  have dv_cache_0017 : y ∉ ((synWbr (synCsn (.cv z)) (synCpw1fn) (.cv x))).fv :=
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
  have dv_cache_0018 : x ∉ ((synCpw (synCpw1 (synCpw (synCfdif R A X))))).fv :=
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
  have dv_cache_0019 : x ∉ ((synCpw1 (synCpw (synCfdif R A X)))).fv :=
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
  have dv_cache_0020 : y ∉ ((synCpw1 (synCpw (synCfdif R A X)))).fv :=
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
  have dv_cache_0021 : z ∉ ((synCfdif R A X)).fv :=
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
  have dv_cache_0022 : y ∉ ((synCpw (synCfdif R A X))).fv :=
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
  have dv_cache_0023 : x ∉ ((synCpw (synCpw1 (synCfdif R A X)))).fv :=
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
  have dv_cache_0025 : e ∉ ((synCfdif R A X)).fv :=
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
  have dv_cache_0026 : e ∉ ((Wff.classMem (.cv q) (synCpw1 (synCfdif R A X)))).fv :=
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
      ((synWa (synWa (.classMem (.cv q) (synCpw1 (synCfdif R A X)))
            (.classMem (.cv e) (synCfdif R A X))) (.classEq (.cv q) (synCsn (.cv e))))).fv :=
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
      ((synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synCfdif R A X)))
              (.classMem (.cv e) (synCfdif R A X))) (.classEq (.cv q) (synCsn (.cv e))))
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
      ((Wff.imp (.classMem (.cv e) (synCsep2 (.cv x) (.cv y)))
          (synWbr (.cv d) R (.cv e)))).fv :=
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
      ((Wff.imp (.classMem (.cv d) (synCsep2 (.cv x) (.cv y)))
          (synWbr (.cv e) R (.cv d)))).fv :=
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
      ((synWral a A (synWral b A
            (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a)))
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
      ((synWral a A (synWral b A
            (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a)))
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
      ((Wff.imp (synWa (synWbr (.cv e) R (.cv b)) (synWbr (.cv b) R (.cv e)))
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
      ((Wff.imp (synWa (synWbr (.cv e) R (.cv d)) (synWbr (.cv d) R (.cv e)))
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
    d ∉ ((synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))).fv :=
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
  have dv_cache_0087 : d ∉ ((Wff.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))).fv :=
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
  have dv_cache_0088 : d ∉ ((synCfpiv R A (.cv x) (.cv y))).fv :=
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
  have dv_cache_0089 : d ∉ ((synCsn (.cv e))).fv :=
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
    y ∉ ((synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))).fv :=
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
  have dv_cache_0091 : y ∉ ((Wff.classMem (.cv q) (synCfdpivrange2 R A X))).fv :=
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
    x ∉ ((synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))).fv :=
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
  have dv_cache_0093 : x ∉ ((Wff.classMem (.cv q) (synCfdpivrange2 R A X))).fv :=
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
    e ∉ ((synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))).fv :=
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
  have dv_cache_0095 : e ∉ ((Wff.classMem (.cv q) (synCfdpivrange2 R A X))).fv :=
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
  have dv_cache_0096 : q ∉ ((synCpw1 (synCfdif R A X))).fv :=
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
  have dv_cache_0097 : q ∉ ((synCfdpivrange2 R A X)).fv :=
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
    q ∉ ((synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))).fv :=
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
  have dv_cache_0099 : x ∉ ((synCpw1 (synCfdif R A X))).fv :=
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
  have dv_cache_0100 : y ∉ ((synCpw1 (synCfdif R A X))).fv :=
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
  have dv_cache_0101 : y ∉ ((synCfdpivrange2 R A X)).fv :=
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
  have dv_cache_0102 : x ∉ ((synCnc (synCpw1 (synCfdif R A X)))).fv :=
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
  have dv_cache_0103 : x ∉ ((synCnc (synCfdpivrange2 R A X))).fv :=
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
  have dv_cache_0104 : y ∉ ((synCnc (synCfdpivrange2 R A X))).fv :=
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
  have dv_cache_0105 : x ∉ ((synWss (synCpw1 (synCfdif R A X)) (.cv y))).fv :=
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
    y ∉ ((synWss (synCpw1 (synCfdif R A X)) (synCfdpivrange2 R A X))).fv :=
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
  have dv_cache_0107 : p ∉ ((synCnc (synCpw1 (synCfdif R A X)))).fv :=
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
  have dv_cache_0108 : p ∉ ((synCnc (synChnord X))).fv :=
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
  have dv_cache_0109 : q ∉ ((synCnc (synChnord X))).fv :=
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
  have dv_cache_0114 : h ∉ ((synCpw1 (synCfdif R A X))).fv :=
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
  have dv_cache_0116 : i ∉ ((synChnord X)).fv :=
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
  have dv_cache_0117 : i ∉ ((synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))).fv :=
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
  have dv_cache_0118 : h ∉ ((synWf1o (.cv i) (.cv q) (synChnord X))).fv :=
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
    f ∉ ((synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)))).fv :=
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
      ((synWf1 (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)))
          (synCpw1 (synCfdif R A X)) (synChnord X))).fv :=
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
      ((Wff.imp (synWf1 (.cv g) (.cv p) (.cv q)) (synWex f
            (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))))).fv :=
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
      ((Wff.imp (synWf1 (.cv g) (.cv p) (.cv q)) (synWex f
            (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))))).fv :=
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
    g ∉ ((synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))).fv :=
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
      ((synWa (.classMem (.cv p) (synCnc (synCpw1 (synCfdif R A X))))
          (.classMem (.cv q) (synCnc (synChnord X))))).fv :=
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
  have dv_cache_0125 : q ∉ ((synCnc (synCpw1 (synCfdif R A X)))).fv :=
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
    p ∉ ((synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))).fv :=
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
    q ∉ ((synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))).fv :=
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
  have dv_cache_0128 : f ∉ ((Wff.classEq (.cv a) (synCpw1 (synCfdif R A X)))).fv :=
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
  have dv_cache_0129 : f ∉ ((Wff.classEq (.cv b) (synChnord X))).fv :=
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
  have dv_cache_0130 : a ∉ ((synCpw1 (synCfdif R A X))).fv :=
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
  have dv_cache_0131 : b ∉ ((synCpw1 (synCfdif R A X))).fv :=
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
  have dv_cache_0132 : b ∉ ((synChnord X)).fv :=
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
  have dv_cache_0133 : a ∉ ((synCnc (synCpw1 (synCfdif R A X)))).fv :=
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
  have dv_cache_0134 : a ∉ ((synCnc (synChnord X))).fv :=
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
  have dv_cache_0135 : b ∉ ((synCnc (synChnord X))).fv :=
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
    a ∉ ((synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (.cv b)))).fv :=
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
    b ∉ ((synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))).fv :=
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
  have dv_cache_0140 : f ∉ ((synCpw1 (synCfdif R A X))).fv :=
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
  have dv_cache_0141 : f ∉ ((synChnord X)).fv :=
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
  have dv_cache_0142 : h ∉ ((synChnord X)).fv :=
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
    p ∉ ((synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))).fv :=
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
  have dv_cache_0145 : p ∉ ((synCnc (synCpw (synCpw (synChnord X))))).fv :=
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
  have dv_cache_0146 : q ∉ ((synCnc (synCpw (synCpw (synChnord X))))).fv :=
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
  have dv_cache_0148 : a ∉ ((synCpw (synCpw (synCpw1 (synCfdif R A X))))).fv :=
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
  have dv_cache_0149 : i ∉ ((synCpw (synCpw (synChnord X)))).fv :=
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
      ((synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))).fv :=
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
    a ∉ ((synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))).fv :=
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
    h ∉ ((synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv a)))).fv :=
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
      ((synWf1 (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv a)))
          (synCpw (synCpw (synCpw1 (synCfdif R A X))))
          (synCpw (synCpw (synChnord X))))).fv :=
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
      ((Wff.imp (synWf1 (.cv g) (.cv p) (.cv q)) (synWex h
            (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
              (synCpw (synCpw (synChnord X))))))).fv :=
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
      ((Wff.imp (synWf1 (.cv g) (.cv p) (.cv q)) (synWex h
            (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
              (synCpw (synCpw (synChnord X))))))).fv :=
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
      ((synWex h (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
            (synCpw (synCpw (synChnord X)))))).fv :=
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
      ((synWa (.classMem (.cv p) (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
          (.classMem (.cv q) (synCnc (synCpw (synCpw (synChnord X))))))).fv :=
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
    q ∉ ((synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))).fv :=
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
      ((synWex h (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
            (synCpw (synCpw (synChnord X)))))).fv :=
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
      ((synWex h (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
            (synCpw (synCpw (synChnord X)))))).fv :=
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
    h ∉ ((Wff.classEq (.cv b) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))).fv :=
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
    h ∉ ((Wff.classEq (.cv c) (synCpw (synCpw (synChnord X))))).fv :=
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
  have dv_cache_0163 : b ∉ ((synCpw (synCpw (synCpw1 (synCfdif R A X))))).fv :=
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
  have dv_cache_0164 : c ∉ ((synCpw (synCpw (synCpw1 (synCfdif R A X))))).fv :=
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
  have dv_cache_0165 : c ∉ ((synCpw (synCpw (synChnord X)))).fv :=
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
    b ∉ ((synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))).fv :=
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
  have dv_cache_0167 : b ∉ ((synCnc (synCpw (synCpw (synChnord X))))).fv :=
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
  have dv_cache_0168 : c ∉ ((synCnc (synCpw (synCpw (synChnord X))))).fv :=
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
      ((synWex h (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
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
      ((synWex h (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
            (synCpw (synCpw (synChnord X)))))).fv :=
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
  have dv_cache_0174 : k ∉ ((synCpw1 (synCpw1 (synCpw1 A)))).fv :=
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
  have dv_cache_0175 : k ∉ ((synCpw (synCpw (synChnord X)))).fv :=
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
    (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))))
  let syntaxFormula0001 : Wff :=
    (synWbr (synCtc (synCtc (synCnc A))) (synClec)
      (synCnc (synCpw (synCpw (synCfdif R A X)))))
  let syntaxFormula0002 : Wff :=
    (synWbr (synCtc (synCtc (synCtc (synCnc A)))) (synClec)
      (synCtc (synCnc (synCpw (synCpw (synCfdif R A X))))))
  let syntaxFormula0003 : Wff :=
    (synWf1o (synCres (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
      (synCpw1 (synCpw (synCpw (synCfdif R A X))))
      (synCima (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X))))))
  let syntaxFormula0004 : Wff :=
    (synWrex z (synCpw (synCpw (synCfdif R A X))) (.classEq (.cv x) (synCpw1 (.cv z))))
  let syntaxFormula0005 : Wff :=
    (synWrex y (synCpw1 (synCpw (synCpw (synCfdif R A X))))
      (synWbr (.cv y) (synCpw1fn) (.cv x)))
  let syntaxFormula0006 : Wff :=
    (synWa (.classMem (.cv y) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
      (synWbr (.cv y) (synCpw1fn) (.cv x)))
  let syntaxFormula0007 : Wff :=
    (synWa (.classEq (.cv y) (synCsn (.cv z))) (synWbr (.cv y) (synCpw1fn) (.cv x)))
  let syntaxFormula0008 : Wff :=
    (synWrex z (synCpw (synCpw (synCfdif R A X))) syntaxFormula0007)
  let syntaxFormula0009 : Wff := (synWex y syntaxFormula0007)
  let syntaxFormula0010 : Wff :=
    (synWf1o (synCres (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
      (synCpw1 (synCpw (synCpw (synCfdif R A X))))
      (synCpw (synCpw1 (synCpw (synCfdif R A X)))))
  let syntaxFormula0011 : Wff :=
    (.classMem (synCres (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
      (synCvv))
  let syntaxFormula0012 : Wff :=
    (synWbr (synCpw1 (synCpw (synCpw (synCfdif R A X)))) (synCen)
      (synCpw (synCpw1 (synCpw (synCfdif R A X)))))
  let syntaxFormula0013 : Wff :=
    (synWf1o (synCres (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X))))
      (synCpw1 (synCpw (synCfdif R A X)))
      (synCima (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X)))))
  let syntaxFormula0014 : Wff :=
    (synWrex y (synCpw1 (synCpw (synCfdif R A X))) (synWbr (.cv y) (synCpw1fn) (.cv x)))
  let syntaxFormula0015 : Wff :=
    (synWa (.classMem (.cv y) (synCpw1 (synCpw (synCfdif R A X))))
      (synWbr (.cv y) (synCpw1fn) (.cv x)))
  let syntaxFormula0016 : Wff :=
    (synWrex z (synCpw (synCfdif R A X)) syntaxFormula0007)
  let syntaxFormula0017 : Wff :=
    (synWf1o (synCres (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X))))
      (synCpw1 (synCpw (synCfdif R A X))) (synCpw (synCpw1 (synCfdif R A X))))
  let syntaxFormula0018 : Wff :=
    (.classMem (synCres (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X)))) (synCvv))
  let syntaxFormula0019 : Wff :=
    (synWbr (synCpw1 (synCpw (synCfdif R A X))) (synCen)
      (synCpw (synCpw1 (synCfdif R A X))))
  let syntaxFormula0020 : Wff :=
    (synWbr (synCpw (synCpw1 (synCpw (synCfdif R A X)))) (synCen)
      (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
  let syntaxFormula0021 : Wff :=
    (synWbr (synCpw1 (synCpw (synCpw (synCfdif R A X)))) (synCen)
      (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
  let syntaxFormula0022 : Wff :=
    (synWbr (synCtc (synCtc (synCtc (synCnc A)))) (synClec)
      (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
  let syntaxFormula0023 : Wff :=
    (synWa (.classMem (.cv q) (synCpw1 (synCfdif R A X)))
      (.classMem (.cv e) (synCfdif R A X)))
  let syntaxFormula0024 : Wff :=
    (synWa syntaxFormula0023 (.classEq (.cv q) (synCsn (.cv e))))
  let syntaxFormula0025 : Wff :=
    (synWrex x X (synWrex y X (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))))
  let syntaxFormula0026 : Wff := (synWa syntaxFormula0024 (.classMem (.cv x) X))
  let syntaxFormula0027 : Wff :=
    (synWa syntaxFormula0024 (synWa (.classMem (.cv x) X) (.classMem (.cv y) X)))
  let syntaxFormula0028 : Wff :=
    (synWa syntaxFormula0027 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))))
  let syntaxFormula0029 : Wff :=
    (synWa (synWbr R (synCwe) A) (synWa (.classMem (.cv x) X) (.classMem (.cv y) X)))
  let syntaxFormula0030 : Wff :=
    (synWa (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsn (.cv e))))
  let syntaxFormula0031 : Wff :=
    (.imp (.classMem (.cv d) (synCsn (.cv e)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))
  let syntaxFormula0032 : Wff :=
    (.imp (.classMem (.cv c) (synCsep2 (.cv x) (.cv y))) (synWbr (.cv e) R (.cv c)))
  let syntaxFormula0033 : Wff := (synWral c A syntaxFormula0032)
  let syntaxFormula0034 : Wff :=
    (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 (.cv x) (.cv y))))
      syntaxFormula0033)
  let syntaxFormula0035 : Wff :=
    (synWa (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))
  let syntaxFormula0036 : Wff :=
    (.imp (.classMem (.cv c) (synCsep2 (.cv x) (.cv y))) (synWbr (.cv d) R (.cv c)))
  let syntaxFormula0037 : Wff := (synWral c A syntaxFormula0036)
  let syntaxFormula0038 : Wff :=
    (synWa (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))))
      syntaxFormula0037)
  let syntaxFormula0039 : Wff :=
    (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a)))
      (.classEq (.cv a) (.cv b)))
  let syntaxFormula0040 : Wff := (synWral b A syntaxFormula0039)
  let syntaxFormula0041 : Wff := (synWral a A syntaxFormula0040)
  let syntaxFormula0042 : Wff :=
    (.imp (synWa (synWbr (.cv e) R (.cv d)) (synWbr (.cv d) R (.cv e)))
      (.classEq (.cv e) (.cv d)))
  let syntaxFormula0043 : Wff :=
    (synWb (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsn (.cv e))))
  let syntaxFormula0044 : Wff := (.imp syntaxFormula0031 syntaxFormula0043)
  let syntaxFormula0045 : Wff :=
    (.imp (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv q) (synCfdpivrange2 R A X)))
  let syntaxFormula0046 : Wff := (.imp (.classMem (.cv y) X) syntaxFormula0045)
  let syntaxFormula0047 : Wff := (synWral y X syntaxFormula0045)
  let syntaxFormula0048 : Wff :=
    (.imp (synWrex y X (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv q) (synCfdpivrange2 R A X)))
  let syntaxFormula0049 : Wff := (.imp (.classMem (.cv x) X) syntaxFormula0048)
  let syntaxFormula0050 : Wff := (synWral x X syntaxFormula0048)
  let syntaxFormula0051 : Wff :=
    (.imp (.classEq (.cv q) (synCsn (.cv e))) (.classMem (.cv q) (synCfdpivrange2 R A X)))
  let syntaxFormula0052 : Wff :=
    (.imp (.classMem (.cv e) (synCfdif R A X)) syntaxFormula0051)
  let syntaxFormula0053 : Wff := (synWral e (synCfdif R A X) syntaxFormula0051)
  let syntaxFormula0054 : Wff :=
    (synWa (.classMem (synCfdpivrange2 R A X) (synCnc (synCfdpivrange2 R A X)))
      (synWss (synCpw1 (synCfdif R A X)) (synCfdpivrange2 R A X)))
  let syntaxFormula0055 : Wff :=
    (synWrex x (synCnc (synCpw1 (synCfdif R A X)))
      (synWrex y (synCnc (synCfdpivrange2 R A X)) (synWss (.cv x) (.cv y))))
  let syntaxFormula0056 : Wff :=
    (synWbr (synCnc (synCpw1 (synCfdif R A X))) (synClec)
      (synCnc (synCfdpivrange2 R A X)))
  let syntaxFormula0057 : Wff :=
    (synWbr (synCnc (synCfdpivrange2 R A X)) (synClec)
      (synCnc (synCxp (synCxpk X X) (synCnnc))))
  let syntaxFormula0058 : Wff := (synWa syntaxFormula0056 syntaxFormula0057)
  let syntaxFormula0059 : Wff :=
    (synWa (.classMem (synCnc (synCfdpivrange2 R A X)) (synCncs))
      (.classMem (synCnc (synCxp (synCxpk X X) (synCnnc))) (synCncs)))
  let syntaxFormula0060 : Wff := (.imp syntaxFormula0059 syntaxFormula0059)
  let syntaxFormula0061 : Wff :=
    (synWbr (synCnc (synCpw1 (synCfdif R A X))) (synClec)
      (synCnc (synCxp (synCxpk X X) (synCnnc))))
  let syntaxFormula0062 : Wff := (.imp syntaxFormula0058 syntaxFormula0061)
  let syntaxFormula0063 : Wff :=
    (synWbr (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synClec)
      (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc)))))
  let syntaxFormula0064 : Wff :=
    (synWbr (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X))))) (synClec)
      (synCtc (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc))))))
  let syntaxFormula0065 : Wff :=
    (.classMem (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X)))))
      (synChwcards (synCvv)))
  let syntaxFormula0066 : Wff :=
    (synWbr (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X))))) (synClec)
      (synChncard (synCxp (synCxpk X X) (synCnnc))))
  let syntaxFormula0067 : Wff :=
    (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
      (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X))))))
  let syntaxFormula0068 : Wff := (synWo syntaxFormula0066 syntaxFormula0067)
  let syntaxFormula0069 : Wff :=
    (.classMem (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X))))) (synCncs))
  let syntaxFormula0070 : Wff :=
    (.classMem (synCtc (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc))))) (synCncs))
  let syntaxFormula0071 : Wff :=
    (synW3a (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc))) (synCncs))
      syntaxFormula0069 syntaxFormula0070)
  let syntaxFormula0072 : Wff :=
    (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
      (synCtc (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc))))))
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
    (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
      (synCtc (synCtc (synChncard X))))
  let syntaxFormula0084 : Wff := (synWa syntaxFormula0066 syntaxFormula0083)
  let syntaxFormula0085 : Wff :=
    (synWa (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc))) (synCncs))
      (.classMem (synCtc (synCtc (synChncard X))) (synCncs)))
  let syntaxFormula0086 : Wff := (.imp syntaxFormula0085 syntaxFormula0085)
  let syntaxFormula0087 : Wff :=
    (synWbr (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X))))) (synClec)
      (synCtc (synCtc (synChncard X))))
  let syntaxFormula0088 : Wff := (.imp syntaxFormula0084 syntaxFormula0087)
  let syntaxFormula0089 : Wff :=
    (synWbr (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synClec)
      (synCtc (synChncard X)))
  let syntaxFormula0090 : Wff :=
    (synWbr (synCnc (synCpw1 (synCfdif R A X))) (synClec) (synCnc (synChnord X)))
  let syntaxFormula0091 : Wff :=
    (synWa (.classMem (.cv p) (synCnc (synCpw1 (synCfdif R A X))))
      (.classMem (.cv q) (synCnc (synChnord X))))
  let syntaxFormula0092 : Wff :=
    (synWa (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))
      (synWf1o (.cv i) (.cv q) (synChnord X)))
  let syntaxFormula0093 : Wff :=
    (synW3a (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))
      (synWf1o (.cv i) (.cv q) (synChnord X)) (synWf1 (.cv g) (.cv p) (.cv q)))
  let syntaxFormula0094 : Wff :=
    (synWf1 (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)))
      (synCpw1 (synCfdif R A X)) (synChnord X))
  let syntaxFormula0095 : Wff :=
    (synWa (.classMem (synChnord X) (synCnc (synChnord X)))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))))
  let syntaxFormula0096 : Wff :=
    (synWrex b (synCnc (synChnord X)) (synWex f (synWf1 (.cv f) (.cv a) (.cv b))))
  let syntaxFormula0097 : Wff :=
    (synWrex a (synCnc (synCpw1 (synCfdif R A X))) syntaxFormula0096)
  let syntaxFormula0098 : Wff :=
    (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
      (synCpw (synCpw (synChnord X))))
  let syntaxFormula0099 : Wff := (synWex h syntaxFormula0098)
  let syntaxFormula0100 : Wff :=
    (.classMem (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))) (synCncs))
  let syntaxFormula0101 : Wff :=
    (synWbr (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))) (synClec)
      (synCnc (synCpw (synCpw (synChnord X)))))
  let syntaxFormula0102 : Wff :=
    (synWrex p (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWrex q (synCnc (synCpw (synCpw (synChnord X))))
        (synWex g (synWf1 (.cv g) (.cv p) (.cv q)))))
  let syntaxFormula0103 : Wff :=
    (synWa (.classMem (.cv p) (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
      (.classMem (.cv q) (synCnc (synCpw (synCpw (synChnord X))))))
  let syntaxFormula0104 : Wff :=
    (synWa (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X)))))
  let syntaxFormula0105 : Wff := (synWex a (synWex i syntaxFormula0104))
  let syntaxFormula0106 : Wff :=
    (synW3a (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv g) (.cv p) (.cv q)))
  let syntaxFormula0107 : Wff :=
    (synWf1 (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv a)))
      (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (synCpw (synCpw (synChnord X))))
  let syntaxFormula0108 : Wff :=
    (.classMem (synCpw (synCpw (synChnord X))) (synCnc (synCpw (synCpw (synChnord X)))))
  let syntaxFormula0109 : Wff := (synWa syntaxFormula0108 syntaxFormula0099)
  let syntaxFormula0110 : Wff :=
    (.classMem (synCpw (synCpw (synCpw1 (synCfdif R A X))))
      (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
  let syntaxFormula0111 : Wff :=
    (synWrex c (synCnc (synCpw (synCpw (synChnord X))))
      (synWex h (synWf1 (.cv h) (.cv b) (.cv c))))
  let syntaxFormula0112 : Wff :=
    (synWrex b (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))) syntaxFormula0111)
  let syntaxFormula0113 : Wff := (synWa syntaxFormula0022 syntaxFormula0101)
  let syntaxFormula0114 : Wff :=
    (synWbr (synCtc (synCtc (synCtc (synCnc A)))) (synClec)
      (synCnc (synCpw (synCpw (synChnord X)))))
  let syntaxFormula0115 : Wff := (.imp syntaxFormula0113 syntaxFormula0114)
  have p0000 :=
    @gFdcolcodetc2le2 A X R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0001 := @gSimpl (synWbr R (synCwe) A) (synWss A (synCpw X))
  have p0002 := @gId (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
  have p0003 :=
    @gA1ii
      (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWbr R (synCwe) A))
      syntaxFormula0000 p0001 p0002
  have p0004 := @gSimpr (synWbr R (synCwe) A) (synWss A (synCpw X))
  have p0005 :=
    @gA1ii
      (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWss A (synCpw X)))
      syntaxFormula0000 p0004 p0002
  have p0006 :=
    @gJca (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWbr R (synCwe) A) (synWss A (synCpw X)) p0003 p0005
  have p0007 :=
    @gA1ii
      (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0001)
      syntaxFormula0000 p0000 p0006
  have p0008 :=
    @gFdifex2 A X R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_cfbfdwppcarrierimpndv_1
      hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0009 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWbr R (synCwe) A) (.classMem (synCfdif R A X) (synCvv)) p0003 p0008
  have p0010 := @gPwexg (synCfdif R A X) (synCvv)
  have p0011 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCfdif R A X) (synCvv))
      (.classMem (synCpw (synCfdif R A X)) (synCvv)) p0009 p0010
  have p0012 := @gPwexg (synCpw (synCfdif R A X)) (synCvv)
  have p0013 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw (synCfdif R A X)) (synCvv))
      (.classMem (synCpw (synCpw (synCfdif R A X))) (synCvv)) p0011 p0012
  have p0014 := @gNcelncs (synCpw (synCpw (synCfdif R A X))) (synCvv)
  have p0015 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw (synCpw (synCfdif R A X))) (synCvv))
      (.classMem (synCnc (synCpw (synCpw (synCfdif R A X)))) (synCncs)) p0013 p0014
  have p0016 := @gNcelncs A (synCvv)
  have p0017 := Nominal.mp hyp_cfbfdwppcarrierimpndv_2 p0016
  have p0018 := @gTccl (synCnc A)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 := @gTccl (synCtc (synCnc A))
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @gJctil (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCpw (synCpw (synCfdif R A X)))) (synCncs))
      (.classMem (synCtc (synCtc (synCnc A))) (synCncs)) p0015 p0021
  have p0023 :=
    @gTlecg (synCtc (synCtc (synCnc A)))
      (synCnc (synCpw (synCpw (synCfdif R A X))))
  have p0024 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa (.classMem (synCtc (synCtc (synCnc A))) (synCncs))
        (.classMem (synCnc (synCpw (synCpw (synCfdif R A X)))) (synCncs)))
      (synWb syntaxFormula0001 syntaxFormula0002) p0022 p0023
  have p0025 :=
    @gMpbid (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0001
      syntaxFormula0002 p0007 p0024
  have p0026 := @gTcncg (synCpw (synCpw (synCfdif R A X))) (synCvv)
  have p0027 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw (synCpw (synCfdif R A X))) (synCvv))
      (.classEq (synCtc (synCnc (synCpw (synCpw (synCfdif R A X)))))
        (synCnc (synCpw1 (synCpw (synCpw (synCfdif R A X))))))
      p0013 p0026
  have p0028 := @gPw1fnf1o
  have p0029 := @gF1of1 (synC1c) (synCpw (synC1c)) (synCpw1fn)
  have p0030 := Nominal.mp p0028 p0029
  have p0031 := @gPw1ss1c (synCpw (synCpw (synCfdif R A X)))
  have p0032 :=
    @gF1ores (synC1c) (synCpw (synC1c))
      (synCpw1 (synCpw (synCpw (synCfdif R A X)))) (synCpw1fn)
  have p0033 :=
    @gMp2an (synWf1 (synCpw1fn) (synC1c) (synCpw (synC1c)))
      (synWss (synCpw1 (synCpw (synCpw (synCfdif R A X)))) (synC1c))
      syntaxFormula0003 p0030 p0031 p0032
  have p0034 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma x y (synCpw1fn)
      (synCpw1 (synCpw (synCpw (synCfdif R A X)))) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0035 := @gVex x
  have p0036 := @gElpw (.cv x) (synCpw1 (synCpw (synCfdif R A X))) p0035
  have p0037 :=
    @gSspw1 z (.cv x) (synCpw (synCfdif R A X)) dv_cache_0009 dv_cache_0010 p0035
  have p0038 := (Nominal.biimpRefl syntaxFormula0004)
  have p0039 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw z
      (synCpw (synCfdif R A X)) dv_cache_0010
  have p0040 :=
    @gEqabri (synWss (.cv z) (synCpw (synCfdif R A X))) z
      (synCpw (synCpw (synCfdif R A X))) p0039
  have p0041 :=
    @gAnbi1i (.classMem (.cv z) (synCpw (synCpw (synCfdif R A X))))
      (synWss (.cv z) (synCpw (synCfdif R A X))) (.classEq (.cv x) (synCpw1 (.cv z)))
      p0040
  have p0042 :=
    @gExbii
      (synWa (.classMem (.cv z) (synCpw (synCpw (synCfdif R A X))))
        (.classEq (.cv x) (synCpw1 (.cv z))))
      (synWa (synWss (.cv z) (synCpw (synCfdif R A X)))
        (.classEq (.cv x) (synCpw1 (.cv z))))
      z p0041
  have p0043 :=
    @gBitr2i syntaxFormula0004
      (synWex z (synWa (.classMem (.cv z) (synCpw (synCpw (synCfdif R A X))))
          (.classEq (.cv x) (synCpw1 (.cv z)))))
      (synWex z (synWa (synWss (.cv z) (synCpw (synCfdif R A X)))
          (.classEq (.cv x) (synCpw1 (.cv z)))))
      p0038 p0042
  have p0044 :=
    @gN3bitri (.classMem (.cv x) (synCpw (synCpw1 (synCpw (synCfdif R A X)))))
      (synWss (.cv x) (synCpw1 (synCpw (synCfdif R A X))))
      (synWex z (synWa (synWss (.cv z) (synCpw (synCfdif R A X)))
          (.classEq (.cv x) (synCpw1 (.cv z)))))
      syntaxFormula0004 p0036 p0037 p0043
  have p0045 := (Nominal.biimpRefl syntaxFormula0005)
  have p0046 :=
    @gElpw1 z (.cv y) (synCpw (synCpw (synCfdif R A X))) dv_cache_0011 dv_cache_0012
  have p0047 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
      (synWrex z (synCpw (synCpw (synCfdif R A X))) (.classEq (.cv y) (synCsn (.cv z))))
      (synWbr (.cv y) (synCpw1fn) (.cv x)) p0046
  have p0048 :=
    @gR1941v (.classEq (.cv y) (synCsn (.cv z))) (synWbr (.cv y) (synCpw1fn) (.cv x))
      z (synCpw (synCpw (synCfdif R A X))) dv_cache_0013
  have p0049 :=
    @gBitr4i syntaxFormula0006
      (synWa (synWrex z (synCpw (synCpw (synCfdif R A X)))
          (.classEq (.cv y) (synCsn (.cv z)))) (synWbr (.cv y) (synCpw1fn) (.cv x)))
      syntaxFormula0008 p0047 p0048
  have p0050 := @gExbii syntaxFormula0006 syntaxFormula0008 y p0049
  have p0051 :=
    @gRexcom4 syntaxFormula0007 z y (synCpw (synCpw (synCfdif R A X))) dv_cache_0014
      dv_cache_0015
  have p0052 := @gSnex (.cv z)
  have p0053 := @gBreq1 (.cv y) (synCsn (.cv z)) (.cv x) (synCpw1fn)
  have p0054 :=
    @gCeqsexv (synWbr (.cv y) (synCpw1fn) (.cv x))
      (synWbr (synCsn (.cv z)) (synCpw1fn) (.cv x)) y (synCsn (.cv z)) dv_cache_0016
      dv_cache_0017 p0052 p0053
  have p0055 := @gVex z
  have p0056 := @gBrpw1fn (.cv z) (.cv x) p0055
  have p0057 :=
    @gBitri syntaxFormula0009 (synWbr (synCsn (.cv z)) (synCpw1fn) (.cv x))
      (.classEq (.cv x) (synCpw1 (.cv z))) p0054 p0056
  have p0058 :=
    @gRexbii syntaxFormula0009 (.classEq (.cv x) (synCpw1 (.cv z))) z
      (synCpw (synCpw (synCfdif R A X))) p0057
  have p0059 :=
    @gBitr3i (synWex y syntaxFormula0008)
      (synWrex z (synCpw (synCpw (synCfdif R A X))) syntaxFormula0009)
      syntaxFormula0004 p0051 p0058
  have p0060 :=
    @gN3bitri syntaxFormula0005 (synWex y syntaxFormula0006)
      (synWex y syntaxFormula0008) syntaxFormula0004 p0045 p0050 p0059
  have p0061 :=
    @gBitr4i (.classMem (.cv x) (synCpw (synCpw1 (synCpw (synCfdif R A X)))))
      syntaxFormula0004 syntaxFormula0005 p0044 p0060
  have p0062 :=
    @gEqabi syntaxFormula0005 x (synCpw (synCpw1 (synCpw (synCfdif R A X))))
      dv_cache_0018 p0061
  have p0063 :=
    @gEqtr4i (synCima (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
      (.cab x syntaxFormula0005) (synCpw (synCpw1 (synCpw (synCfdif R A X)))) p0034
      p0062
  have p0064 :=
    @gF1oeq3 (synCima (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
      (synCpw (synCpw1 (synCpw (synCfdif R A X))))
      (synCpw1 (synCpw (synCpw (synCfdif R A X))))
      (synCres (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
  have p0065 := Nominal.mp p0063 p0064
  have p0066 := @gMpbi syntaxFormula0003 syntaxFormula0010 p0033 p0065
  have p0067 := @gId syntaxFormula0010
  have p0068 := @gPw1fnex
  have p0069 := @gPw1exg (synCpw (synCpw (synCfdif R A X))) (synCvv)
  have p0070 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw (synCpw (synCfdif R A X))) (synCvv))
      (.classMem (synCpw1 (synCpw (synCpw (synCfdif R A X)))) (synCvv)) p0013 p0069
  have p0071 :=
    @gResexg (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X)))) (synCvv)
      (synCvv)
  have p0072 :=
    @gSylancr (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1fn) (synCvv))
      (.classMem (synCpw1 (synCpw (synCpw (synCfdif R A X)))) (synCvv))
      syntaxFormula0011 p0068 p0070 p0071
  have p0073 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0011
      syntaxFormula0010 p0072
  have p0074 :=
    @gF1oeng (synCpw1 (synCpw (synCpw (synCfdif R A X))))
      (synCpw (synCpw1 (synCpw (synCfdif R A X)))) (synCvv)
      (synCres (synCpw1fn) (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
  have p0075 := @gEx syntaxFormula0011 syntaxFormula0010 syntaxFormula0012 p0074
  have p0076 :=
    @gSyl56 syntaxFormula0010 syntaxFormula0010
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0011
      (.imp syntaxFormula0010 syntaxFormula0012) p0067 p0073 p0075
  have p0077 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0010
      syntaxFormula0012 p0076
  have p0078 :=
    @gMpi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0010
      syntaxFormula0012 p0066 p0077
  have p0082 := @gPw1ss1c (synCpw (synCfdif R A X))
  have p0083 :=
    @gF1ores (synC1c) (synCpw (synC1c)) (synCpw1 (synCpw (synCfdif R A X)))
      (synCpw1fn)
  have p0084 :=
    @gMp2an (synWf1 (synCpw1fn) (synC1c) (synCpw (synC1c)))
      (synWss (synCpw1 (synCpw (synCfdif R A X))) (synC1c)) syntaxFormula0013 p0030
      p0082 p0083
  have p0085 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma x y (synCpw1fn)
      (synCpw1 (synCpw (synCfdif R A X))) dv_cache_0004 dv_cache_0005 dv_cache_0019
      dv_cache_0020 dv_cache_0008
  have p0087 := @gElpw (.cv x) (synCpw1 (synCfdif R A X)) p0035
  have p0088 := @gSspw1 z (.cv x) (synCfdif R A X) dv_cache_0009 dv_cache_0021 p0035
  have p0089 :=
    (Nominal.biimpRefl
      (synWrex z (synCpw (synCfdif R A X)) (.classEq (.cv x) (synCpw1 (.cv z)))))
  have p0090 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw z
      (synCfdif R A X) dv_cache_0021
  have p0091 :=
    @gEqabri (synWss (.cv z) (synCfdif R A X)) z (synCpw (synCfdif R A X)) p0090
  have p0092 :=
    @gAnbi1i (.classMem (.cv z) (synCpw (synCfdif R A X)))
      (synWss (.cv z) (synCfdif R A X)) (.classEq (.cv x) (synCpw1 (.cv z))) p0091
  have p0093 :=
    @gExbii
      (synWa (.classMem (.cv z) (synCpw (synCfdif R A X)))
        (.classEq (.cv x) (synCpw1 (.cv z))))
      (synWa (synWss (.cv z) (synCfdif R A X)) (.classEq (.cv x) (synCpw1 (.cv z)))) z
      p0092
  have p0094 :=
    @gBitr2i
      (synWrex z (synCpw (synCfdif R A X)) (.classEq (.cv x) (synCpw1 (.cv z))))
      (synWex z (synWa (.classMem (.cv z) (synCpw (synCfdif R A X)))
          (.classEq (.cv x) (synCpw1 (.cv z)))))
      (synWex z (synWa (synWss (.cv z) (synCfdif R A X))
          (.classEq (.cv x) (synCpw1 (.cv z)))))
      p0089 p0093
  have p0095 :=
    @gN3bitri (.classMem (.cv x) (synCpw (synCpw1 (synCfdif R A X))))
      (synWss (.cv x) (synCpw1 (synCfdif R A X)))
      (synWex z (synWa (synWss (.cv z) (synCfdif R A X))
          (.classEq (.cv x) (synCpw1 (.cv z)))))
      (synWrex z (synCpw (synCfdif R A X)) (.classEq (.cv x) (synCpw1 (.cv z)))) p0087
      p0088 p0094
  have p0096 := (Nominal.biimpRefl syntaxFormula0014)
  have p0097 := @gElpw1 z (.cv y) (synCpw (synCfdif R A X)) dv_cache_0011 dv_cache_0010
  have p0098 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 (synCpw (synCfdif R A X))))
      (synWrex z (synCpw (synCfdif R A X)) (.classEq (.cv y) (synCsn (.cv z))))
      (synWbr (.cv y) (synCpw1fn) (.cv x)) p0097
  have p0099 :=
    @gR1941v (.classEq (.cv y) (synCsn (.cv z))) (synWbr (.cv y) (synCpw1fn) (.cv x))
      z (synCpw (synCfdif R A X)) dv_cache_0013
  have p0100 :=
    @gBitr4i syntaxFormula0015
      (synWa (synWrex z (synCpw (synCfdif R A X)) (.classEq (.cv y) (synCsn (.cv z))))
        (synWbr (.cv y) (synCpw1fn) (.cv x)))
      syntaxFormula0016 p0098 p0099
  have p0101 := @gExbii syntaxFormula0015 syntaxFormula0016 y p0100
  have p0102 :=
    @gRexcom4 syntaxFormula0007 z y (synCpw (synCfdif R A X)) dv_cache_0022
      dv_cache_0015
  have p0109 :=
    @gRexbii syntaxFormula0009 (.classEq (.cv x) (synCpw1 (.cv z))) z
      (synCpw (synCfdif R A X)) p0057
  have p0110 :=
    @gBitr3i (synWex y syntaxFormula0016)
      (synWrex z (synCpw (synCfdif R A X)) syntaxFormula0009)
      (synWrex z (synCpw (synCfdif R A X)) (.classEq (.cv x) (synCpw1 (.cv z)))) p0102
      p0109
  have p0111 :=
    @gN3bitri syntaxFormula0014 (synWex y syntaxFormula0015)
      (synWex y syntaxFormula0016)
      (synWrex z (synCpw (synCfdif R A X)) (.classEq (.cv x) (synCpw1 (.cv z)))) p0096
      p0101 p0110
  have p0112 :=
    @gBitr4i (.classMem (.cv x) (synCpw (synCpw1 (synCfdif R A X))))
      (synWrex z (synCpw (synCfdif R A X)) (.classEq (.cv x) (synCpw1 (.cv z))))
      syntaxFormula0014 p0095 p0111
  have p0113 :=
    @gEqabi syntaxFormula0014 x (synCpw (synCpw1 (synCfdif R A X))) dv_cache_0023
      p0112
  have p0114 :=
    @gEqtr4i (synCima (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X))))
      (.cab x syntaxFormula0014) (synCpw (synCpw1 (synCfdif R A X))) p0085 p0113
  have p0115 :=
    @gF1oeq3 (synCima (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X))))
      (synCpw (synCpw1 (synCfdif R A X))) (synCpw1 (synCpw (synCfdif R A X)))
      (synCres (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X))))
  have p0116 := Nominal.mp p0114 p0115
  have p0117 := @gMpbi syntaxFormula0013 syntaxFormula0017 p0084 p0116
  have p0118 := @gId syntaxFormula0017
  have p0120 := @gPw1exg (synCpw (synCfdif R A X)) (synCvv)
  have p0121 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw (synCfdif R A X)) (synCvv))
      (.classMem (synCpw1 (synCpw (synCfdif R A X))) (synCvv)) p0011 p0120
  have p0122 :=
    @gResexg (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X))) (synCvv) (synCvv)
  have p0123 :=
    @gSylancr (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1fn) (synCvv))
      (.classMem (synCpw1 (synCpw (synCfdif R A X))) (synCvv)) syntaxFormula0018 p0068
      p0121 p0122
  have p0124 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0018
      syntaxFormula0017 p0123
  have p0125 :=
    @gF1oeng (synCpw1 (synCpw (synCfdif R A X)))
      (synCpw (synCpw1 (synCfdif R A X))) (synCvv)
      (synCres (synCpw1fn) (synCpw1 (synCpw (synCfdif R A X))))
  have p0126 := @gEx syntaxFormula0018 syntaxFormula0017 syntaxFormula0019 p0125
  have p0127 :=
    @gSyl56 syntaxFormula0017 syntaxFormula0017
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0018
      (.imp syntaxFormula0017 syntaxFormula0019) p0118 p0124 p0126
  have p0128 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0017
      syntaxFormula0019 p0127
  have p0129 :=
    @gMpi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0017
      syntaxFormula0019 p0117 p0128
  have p0130 :=
    @gEnpw (synCpw1 (synCpw (synCfdif R A X))) (synCpw (synCpw1 (synCfdif R A X)))
  have p0131 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0019
      syntaxFormula0020 p0129 p0130
  have p0132 :=
    @gJca (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0012
      syntaxFormula0020 p0078 p0131
  have p0133 :=
    @gEntr (synCpw1 (synCpw (synCpw (synCfdif R A X))))
      (synCpw (synCpw1 (synCpw (synCfdif R A X))))
      (synCpw (synCpw (synCpw1 (synCfdif R A X))))
  have p0134 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa syntaxFormula0012 syntaxFormula0020) syntaxFormula0021 p0132 p0133
  have p0135 :=
    @gEqncg (synCpw1 (synCpw (synCpw (synCfdif R A X))))
      (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (synCvv)
  have p0136 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1 (synCpw (synCpw (synCfdif R A X)))) (synCvv))
      (synWb (.classEq (synCnc (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
          (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))) syntaxFormula0021)
      p0070 p0135
  have p0137 :=
    @gMpbird (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classEq (synCnc (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
        (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
      syntaxFormula0021 p0134 p0136
  have p0138 :=
    @gEqtrd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synCtc (synCnc (synCpw (synCpw (synCfdif R A X)))))
      (synCnc (synCpw1 (synCpw (synCpw (synCfdif R A X)))))
      (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))) p0027 p0137
  have p0139 :=
    @gBreq2d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synCtc (synCnc (synCpw (synCpw (synCfdif R A X)))))
      (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synCtc (synCtc (synCtc (synCnc A)))) (synClec) p0138
  have p0140 :=
    @gMpbid (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0002
      syntaxFormula0022 p0025 p0139
  have p0141 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0022
      (synWwpp) p0140
  have p0142 := @gElpw1 e (.cv q) (synCfdif R A X) dv_cache_0024 dv_cache_0025
  have p0143 :=
    @gBiimpi (.classMem (.cv q) (synCpw1 (synCfdif R A X)))
      (synWrex e (synCfdif R A X) (.classEq (.cv q) (synCsn (.cv e)))) p0142
  have p0144 := @gNfv (.classMem (.cv q) (synCpw1 (synCfdif R A X))) e dv_cache_0026
  have p0145 := @gNfri (.classMem (.cv q) (synCpw1 (synCfdif R A X))) e p0144
  have p0146 := @gSimpl syntaxFormula0023 (.classEq (.cv q) (synCsn (.cv e)))
  have p0147 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synCfdif R A X)))
      (.classMem (.cv e) (synCfdif R A X))
  have p0148 :=
    @gSyl syntaxFormula0024 syntaxFormula0023 (.classMem (.cv e) (synCfdif R A X)) p0146
      p0147
  have p0149 :=
    @gElfdif x y A X R e dv_cache_0001 dv_cache_0002 dv_cache_0027 dv_cache_0028
      dv_cache_0029 dv_cache_0003 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0008
  have p0150 :=
    @gBiimpi (.classMem (.cv e) (synCfdif R A X))
      (synWa (.classMem (.cv e) A) syntaxFormula0025) p0149
  have p0151 := @gSimpr (.classMem (.cv e) A) syntaxFormula0025
  have p0152 :=
    @gSyl (.classMem (.cv e) (synCfdif R A X))
      (synWa (.classMem (.cv e) A) syntaxFormula0025) syntaxFormula0025 p0150 p0151
  have p0153 :=
    @gSyl syntaxFormula0024 (.classMem (.cv e) (synCfdif R A X)) syntaxFormula0025 p0148
      p0152
  have p0154 := @gNfv syntaxFormula0024 x dv_cache_0038
  have p0155 := @gNfri syntaxFormula0024 x p0154
  have p0156 := @gNfv syntaxFormula0026 y dv_cache_0039
  have p0157 := @gNfri syntaxFormula0026 y p0156
  have p0158 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWbr R (synCwe) A) syntaxFormula0028 p0003
  have p0159 :=
    @gSimpl syntaxFormula0027 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
  have p0160 :=
    @gSimpr syntaxFormula0024 (synWa (.classMem (.cv x) X) (.classMem (.cv y) X))
  have p0161 := @gSimpl (.classMem (.cv x) X) (.classMem (.cv y) X)
  have p0162 :=
    @gSyl syntaxFormula0027 (synWa (.classMem (.cv x) X) (.classMem (.cv y) X))
      (.classMem (.cv x) X) p0160 p0161
  have p0163 :=
    @gSyl syntaxFormula0028 syntaxFormula0027 (.classMem (.cv x) X) p0159 p0162
  have p0166 := @gSimpr (.classMem (.cv x) X) (.classMem (.cv y) X)
  have p0167 :=
    @gSyl syntaxFormula0027 (synWa (.classMem (.cv x) X) (.classMem (.cv y) X))
      (.classMem (.cv y) X) p0160 p0166
  have p0168 :=
    @gSyl syntaxFormula0028 syntaxFormula0027 (.classMem (.cv y) X) p0159 p0167
  have p0169 :=
    @gJca syntaxFormula0028 (.classMem (.cv x) X) (.classMem (.cv y) X) p0163 p0168
  have p0170 :=
    @g_pm3_2 (synWbr R (synCwe) A) (synWa (.classMem (.cv x) X) (.classMem (.cv y) X))
  have p0171 :=
    @gSyl5 syntaxFormula0028 (synWa (.classMem (.cv x) X) (.classMem (.cv y) X))
      (synWbr R (synCwe) A) syntaxFormula0029 p0169 p0170
  have p0172 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (synWbr R (synCwe) A) (.imp syntaxFormula0028 syntaxFormula0029) p0158 p0171
  have p0173 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      syntaxFormula0029 p0172
  have p0174 :=
    @gFdpivinrange A X (.cv x) (.cv y) R dv_cache_0001 dv_cache_0040 dv_cache_0041
      dv_cache_0002 dv_cache_0042 dv_cache_0043 dv_cache_0003 dv_cache_0044 dv_cache_0045
      dv_cache_0046 hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2
      hyp_cfbfdwppcarrierimpndv_3
  have p0175 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      syntaxFormula0029
      (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X)) p0173 p0174
  have p0177 :=
    @gSimpl syntaxFormula0024 (synWa (.classMem (.cv x) X) (.classMem (.cv y) X))
  have p0178 := @gSyl syntaxFormula0028 syntaxFormula0027 syntaxFormula0024 p0159 p0177
  have p0179 := @gSimpr syntaxFormula0023 (.classEq (.cv q) (synCsn (.cv e)))
  have p0180 :=
    @gSyl syntaxFormula0028 syntaxFormula0024 (.classEq (.cv q) (synCsn (.cv e))) p0178
      p0179
  have p0181 :=
    @gSimpr syntaxFormula0027 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
  have p0182 :=
    @gSimpl (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsn (.cv e)))
  have p0183 :=
    @gSimpr (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsn (.cv e)))
  have p0184 := @gElsn d (.cv e) dv_cache_0047
  have p0185 :=
    @gA1i (synWb (.classMem (.cv d) (synCsn (.cv e))) (.classEq (.cv d) (.cv e)))
      syntaxFormula0030 p0184
  have p0186 :=
    @gMpbid syntaxFormula0030 (.classMem (.cv d) (synCsn (.cv e)))
      (.classEq (.cv d) (.cv e)) p0183 p0185
  have p0187 :=
    @gEleq1d syntaxFormula0030 (.cv d) (.cv e) (synCfpiv R A (.cv x) (.cv y)) p0186
  have p0188 :=
    @gMpbird syntaxFormula0030 (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) p0182 p0187
  have p0189 :=
    @gEx (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsn (.cv e)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) p0188
  have p0190 :=
    @gA1d (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0031
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) p0189
  have p0191 :=
    @gSimpl (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
  have p0192 :=
    @gElfpiv A (.cv x) (.cv y) R e c dv_cache_0040 dv_cache_0041 dv_cache_0002
      dv_cache_0048 dv_cache_0027 dv_cache_0044 dv_cache_0045 dv_cache_0049 dv_cache_0050
      dv_cache_0046 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0033 dv_cache_0054
  have p0193 :=
    @gBiimpi (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0034 p0192
  have p0194 :=
    @gSimplr (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 (.cv x) (.cv y)))
      syntaxFormula0033
  have p0195 :=
    @gSyl (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0034
      (.classMem (.cv e) (synCsep2 (.cv x) (.cv y))) p0193 p0194
  have p0196 :=
    @gSyl syntaxFormula0035 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) (synCsep2 (.cv x) (.cv y))) p0191 p0195
  have p0200 :=
    @gSimpll (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 (.cv x) (.cv y)))
      syntaxFormula0033
  have p0201 :=
    @gSyl (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0034
      (.classMem (.cv e) A) p0193 p0200
  have p0202 :=
    @gSyl syntaxFormula0035 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) A) p0191 p0201
  have p0203 :=
    @gSimpr (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
  have p0204 :=
    @gElfpiv A (.cv x) (.cv y) R d c dv_cache_0040 dv_cache_0041 dv_cache_0002
      dv_cache_0048 dv_cache_0055 dv_cache_0044 dv_cache_0045 dv_cache_0049 dv_cache_0056
      dv_cache_0046 dv_cache_0051 dv_cache_0057 dv_cache_0053 dv_cache_0058 dv_cache_0059
  have p0205 :=
    @gBiimpi (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0038 p0204
  have p0206 :=
    @gSimpr
      (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))))
      syntaxFormula0037
  have p0207 :=
    @gSyl (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0038
      syntaxFormula0037 p0205 p0206
  have p0208 :=
    @gSyl syntaxFormula0035 (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      syntaxFormula0037 p0203 p0207
  have p0209 :=
    @gJca syntaxFormula0035 (.classMem (.cv e) A) syntaxFormula0037 p0202 p0208
  have p0210 := @gId (.classEq (.cv c) (.cv e))
  have p0211 :=
    @gEleq1d (.classEq (.cv c) (.cv e)) (.cv c) (.cv e) (synCsep2 (.cv x) (.cv y)) p0210
  have p0213 := @gBreq2d (.classEq (.cv c) (.cv e)) (.cv c) (.cv e) (.cv d) R p0210
  have p0214 :=
    @gImbi12d (.classEq (.cv c) (.cv e)) (.classMem (.cv c) (synCsep2 (.cv x) (.cv y)))
      (.classMem (.cv e) (synCsep2 (.cv x) (.cv y))) (synWbr (.cv d) R (.cv c))
      (synWbr (.cv d) R (.cv e)) p0211 p0213
  have p0215 :=
    @gRspcva syntaxFormula0036
      (.imp (.classMem (.cv e) (synCsep2 (.cv x) (.cv y))) (synWbr (.cv d) R (.cv e))) c
      (.cv e) A dv_cache_0060 dv_cache_0048 dv_cache_0061 p0214
  have p0216 :=
    @gSyl syntaxFormula0035 (synWa (.classMem (.cv e) A) syntaxFormula0037)
      (.imp (.classMem (.cv e) (synCsep2 (.cv x) (.cv y))) (synWbr (.cv d) R (.cv e)))
      p0209 p0215
  have p0217 :=
    @gMpd syntaxFormula0035 (.classMem (.cv e) (synCsep2 (.cv x) (.cv y)))
      (synWbr (.cv d) R (.cv e)) p0196 p0216
  have p0221 :=
    @gSimplr (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 (.cv x) (.cv y)))
      syntaxFormula0037
  have p0222 :=
    @gSyl (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0038
      (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))) p0205 p0221
  have p0223 :=
    @gSyl syntaxFormula0035 (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))) p0203 p0222
  have p0227 :=
    @gSimpll (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 (.cv x) (.cv y)))
      syntaxFormula0037
  have p0228 :=
    @gSyl (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0038
      (.classMem (.cv d) A) p0205 p0227
  have p0229 :=
    @gSyl syntaxFormula0035 (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) A) p0203 p0228
  have p0233 :=
    @gSimpr
      (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 (.cv x) (.cv y))))
      syntaxFormula0033
  have p0234 :=
    @gSyl (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0034
      syntaxFormula0033 p0193 p0233
  have p0235 :=
    @gSyl syntaxFormula0035 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      syntaxFormula0033 p0191 p0234
  have p0236 :=
    @gJca syntaxFormula0035 (.classMem (.cv d) A) syntaxFormula0033 p0229 p0235
  have p0237 := @gId (.classEq (.cv c) (.cv d))
  have p0238 :=
    @gEleq1d (.classEq (.cv c) (.cv d)) (.cv c) (.cv d) (synCsep2 (.cv x) (.cv y)) p0237
  have p0240 := @gBreq2d (.classEq (.cv c) (.cv d)) (.cv c) (.cv d) (.cv e) R p0237
  have p0241 :=
    @gImbi12d (.classEq (.cv c) (.cv d)) (.classMem (.cv c) (synCsep2 (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))) (synWbr (.cv e) R (.cv c))
      (synWbr (.cv e) R (.cv d)) p0238 p0240
  have p0242 :=
    @gRspcva syntaxFormula0032
      (.imp (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))) (synWbr (.cv e) R (.cv d))) c
      (.cv d) A dv_cache_0062 dv_cache_0048 dv_cache_0063 p0241
  have p0243 :=
    @gSyl syntaxFormula0035 (synWa (.classMem (.cv d) A) syntaxFormula0033)
      (.imp (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))) (synWbr (.cv e) R (.cv d)))
      p0236 p0242
  have p0244 :=
    @gMpd syntaxFormula0035 (.classMem (.cv d) (synCsep2 (.cv x) (.cv y)))
      (synWbr (.cv e) R (.cv d)) p0223 p0243
  have p0245 :=
    @gA1d syntaxFormula0035 (synWbr (.cv e) R (.cv d)) (synWbr (.cv d) R (.cv e)) p0244
  have p0246 := @gAncom (synWbr (.cv d) R (.cv e)) (synWbr (.cv e) R (.cv d))
  have p0247 := @gWppweantisym A R
  have p0248 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWbr R (synCwe) A) (synWbr R (synCantisym) A) p0003 p0247
  have p0249 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWbr R (synCantisym) A) syntaxFormula0035 p0248
  have p0250 := @gBrex R A (synCantisym)
  have p0251 := @gBreq (.cv a) (.cv b) (.cv r) R
  have p0252 := @gBreq (.cv b) (.cv a) (.cv r) R
  have p0253 :=
    @gAnbi12d (.classEq (.cv r) R) (synWbr (.cv a) (.cv r) (.cv b))
      (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) (.cv r) (.cv a))
      (synWbr (.cv b) R (.cv a)) p0251 p0252
  have p0254 :=
    @gImbi1d (.classEq (.cv r) R)
      (synWa (synWbr (.cv a) (.cv r) (.cv b)) (synWbr (.cv b) (.cv r) (.cv a)))
      (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a))) (.objEq a b) p0253
  have p0255 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (.imp (synWa (synWbr (.cv a) (.cv r) (.cv b)) (synWbr (.cv b) (.cv r) (.cv a)))
        (.objEq a b))
      (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a))) (.objEq a b))
      a b (.cv c) (.cv c) dv_cache_0064 dv_cache_0065 p0254
  have p0256 :=
    @gRaleq
      (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a))) (.objEq a b))
      b (.cv c) A dv_cache_0066 dv_cache_0067
  have p0257 :=
    @gRaleqbi1dv
      (synWral b (.cv c) (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a)))
          (.objEq a b)))
      (synWral b A (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a)))
          (.objEq a b)))
      a (.cv c) A dv_cache_0068 dv_cache_0069 p0256
  have p0258 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAntisym a b r c
      dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
  have p0259 :=
    @gBrabg
      (synWral a (.cv c) (synWral b (.cv c) (.imp
            (synWa (synWbr (.cv a) (.cv r) (.cv b)) (synWbr (.cv b) (.cv r) (.cv a)))
            (.objEq a b))))
      (synWral a (.cv c) (synWral b (.cv c)
          (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a))) (.objEq a b))))
      (synWral a A (synWral b A
          (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a))) (.objEq a b))))
      r c R A (synCvv) (synCvv) (synCantisym) dv_cache_0076 dv_cache_0053 dv_cache_0077
      dv_cache_0048 dv_cache_0078 dv_cache_0079 dv_cache_0080 p0255 p0257 p0258
  have p0260 :=
    @gSyl (synWbr R (synCantisym) A)
      (synWa (.classMem R (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr R (synCantisym) A) (synWral a A (synWral b A
            (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a)))
              (.objEq a b)))))
      p0250 p0259
  have p0261 :=
    @gIbi (synWbr R (synCantisym) A)
      (synWral a A (synWral b A
          (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a))) (.objEq a b))))
      p0260
  have p0262_e01_recanon :
    Nominal.NPrf (.imp (synWbr R (synCantisym) A) syntaxFormula0041) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWbr, synCop, synCun, synCnin, synWnan, synWa, synCcompl,
          synWrex, synWex, synCphi, synCantisym, synCopab, synWral]
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
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      (synWbr R (synCantisym) A) syntaxFormula0041 p0249 p0262_e01_recanon
  have p0263 :=
    @gSimpl (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
  have p0264 :=
    @gElfpiv A (.cv x) (.cv y) R e c dv_cache_0040 dv_cache_0041 dv_cache_0002
      dv_cache_0048 dv_cache_0027 dv_cache_0044 dv_cache_0045 dv_cache_0049 dv_cache_0050
      dv_cache_0046 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0033 dv_cache_0054
  have p0265 :=
    @gBiimpi (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0034 p0264
  have p0266 :=
    @gSimpll (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 (.cv x) (.cv y)))
      syntaxFormula0033
  have p0267 :=
    @gSyl (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0034
      (.classMem (.cv e) A) p0265 p0266
  have p0268 :=
    @gSyl syntaxFormula0035 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) A) p0263 p0267
  have p0269 :=
    @gSimpr (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
  have p0270 :=
    @gElfpiv A (.cv x) (.cv y) R d c dv_cache_0040 dv_cache_0041 dv_cache_0002
      dv_cache_0048 dv_cache_0055 dv_cache_0044 dv_cache_0045 dv_cache_0049 dv_cache_0056
      dv_cache_0046 dv_cache_0051 dv_cache_0057 dv_cache_0053 dv_cache_0058 dv_cache_0059
  have p0271 :=
    @gBiimpi (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0038 p0270
  have p0272 :=
    @gSimpll (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 (.cv x) (.cv y)))
      syntaxFormula0037
  have p0273 :=
    @gSyl (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0038
      (.classMem (.cv d) A) p0271 p0272
  have p0274 :=
    @gSyl syntaxFormula0035 (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) A) p0269 p0273
  have p0275 := @gBreq1 (.cv a) (.cv e) (.cv b) R
  have p0276 := @gBreq2 (.cv a) (.cv e) (.cv b) R
  have p0277 :=
    @gAnbi12d (.classEq (.cv a) (.cv e)) (synWbr (.cv a) R (.cv b))
      (synWbr (.cv e) R (.cv b)) (synWbr (.cv b) R (.cv a)) (synWbr (.cv b) R (.cv e))
      p0275 p0276
  have p0278 := @gEqeq1 (.cv a) (.cv e) (.cv b)
  have p0279_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv e)) (synWb (.objEq a b) (.classEq (.cv e) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb]
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
    @gImbi12d (.classEq (.cv a) (.cv e))
      (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a)))
      (synWa (synWbr (.cv e) R (.cv b)) (synWbr (.cv b) R (.cv e))) (.objEq a b)
      (.classEq (.cv e) (.cv b)) p0277 p0279_e01_recanon
  have p0280 := @gBreq2 (.cv b) (.cv d) (.cv e) R
  have p0281 := @gBreq1 (.cv b) (.cv d) (.cv e) R
  have p0282 :=
    @gAnbi12d (.classEq (.cv b) (.cv d)) (synWbr (.cv e) R (.cv b))
      (synWbr (.cv e) R (.cv d)) (synWbr (.cv b) R (.cv e)) (synWbr (.cv d) R (.cv e))
      p0280 p0281
  have p0283 := @gEqeq2 (.cv b) (.cv d) (.cv e)
  have p0284 :=
    @gImbi12d (.classEq (.cv b) (.cv d))
      (synWa (synWbr (.cv e) R (.cv b)) (synWbr (.cv b) R (.cv e)))
      (synWa (synWbr (.cv e) R (.cv d)) (synWbr (.cv d) R (.cv e)))
      (.classEq (.cv e) (.cv b)) (.classEq (.cv e) (.cv d)) p0282 p0283
  have p0285 :=
    @gRspc2v
      (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a))) (.objEq a b))
      syntaxFormula0042
      (.imp (synWa (synWbr (.cv e) R (.cv b)) (synWbr (.cv b) R (.cv e)))
        (.classEq (.cv e) (.cv b)))
      a b (.cv e) (.cv d) A A dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0069
      dv_cache_0069 dv_cache_0067 dv_cache_0084 dv_cache_0085 dv_cache_0075 p0279 p0284
  have p0286 :=
    @gSyl2anc syntaxFormula0035 (.classMem (.cv e) A) (.classMem (.cv d) A)
      (.imp (synWral a A (synWral b A
            (.imp (synWa (synWbr (.cv a) R (.cv b)) (synWbr (.cv b) R (.cv a)))
              (.objEq a b)))) syntaxFormula0042)
      p0268 p0274 p0285
  have p0287_e01_recanon :
    Nominal.NPrf (.imp syntaxFormula0035 (.imp syntaxFormula0041 syntaxFormula0042)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWa, synWral]
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
    @gSylcom (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      syntaxFormula0041 syntaxFormula0042 p0262 p0287_e01_recanon
  have p0288 :=
    @gSyl7bi (synWa (synWbr (.cv d) R (.cv e)) (synWbr (.cv e) R (.cv d)))
      (synWa (synWbr (.cv e) R (.cv d)) (synWbr (.cv d) R (.cv e)))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      (.classEq (.cv e) (.cv d)) p0246 p0287
  have p0289 :=
    @gExp4a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      (synWbr (.cv d) R (.cv e)) (synWbr (.cv e) R (.cv d)) (.classEq (.cv e) (.cv d))
      p0288
  have p0290 :=
    Nominal.ax2 (synWbr (.cv d) R (.cv e)) (synWbr (.cv e) R (.cv d))
      (.classEq (.cv e) (.cv d))
  have p0291 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      (.imp (synWbr (.cv d) R (.cv e))
        (.imp (synWbr (.cv e) R (.cv d)) (.classEq (.cv e) (.cv d))))
      (.imp (.imp (synWbr (.cv d) R (.cv e)) (synWbr (.cv e) R (.cv d)))
        (.imp (synWbr (.cv d) R (.cv e)) (.classEq (.cv e) (.cv d))))
      p0289 p0290
  have p0292 :=
    @gMpdi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      (.imp (synWbr (.cv d) R (.cv e)) (synWbr (.cv e) R (.cv d)))
      (.imp (synWbr (.cv d) R (.cv e)) (.classEq (.cv e) (.cv d))) p0245 p0291
  have p0293 :=
    @gMpdi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      (synWbr (.cv d) R (.cv e)) (.classEq (.cv e) (.cv d)) p0217 p0292
  have p0294 := @gEqcom (.cv e) (.cv d)
  have p0295 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      (.classEq (.cv e) (.cv d)) (.classEq (.cv d) (.cv e)) p0293 p0294
  have p0297 :=
    @gA1i (synWb (.classMem (.cv d) (synCsn (.cv e))) (.classEq (.cv d) (.cv e)))
      syntaxFormula0035 p0184
  have p0298 :=
    @gBiimprd syntaxFormula0035 (.classMem (.cv d) (synCsn (.cv e)))
      (.classEq (.cv d) (.cv e)) p0297
  have p0299 :=
    @gSylcom (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0035
      (.classEq (.cv d) (.cv e)) (.classMem (.cv d) (synCsn (.cv e))) p0295 p0298
  have p0300 :=
    @gExp3a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsn (.cv e))) p0299
  have p0301 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.imp (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
        (.imp (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
          (.classMem (.cv d) (synCsn (.cv e)))))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) p0300
  have p0302 :=
    @gBi3 (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCsn (.cv e)))
  have p0303 :=
    @gSyl8 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.imp (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
        (.classMem (.cv d) (synCsn (.cv e))))
      syntaxFormula0044 p0301 p0302
  have p0304 :=
    Nominal.ax2 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0031
      syntaxFormula0043
  have p0305 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.imp (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0044)
      (.imp (.imp (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0031)
        (.imp (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0043))
      p0303 p0304
  have p0306 :=
    @gMpdi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.imp (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0031)
      (.imp (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0043) p0190
      p0305
  have p0307 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0043 p0306
  have p0308 :=
    @gAlrimdv (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) syntaxFormula0043 d
      dv_cache_0086 dv_cache_0087 p0307
  have p0309 :=
    @gDfcleq d (synCfpiv R A (.cv x) (.cv y)) (synCsn (.cv e)) dv_cache_0088
      dv_cache_0089
  have p0310 :=
    @gSyl6ibr (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) (.all d syntaxFormula0043)
      (.classEq (synCfpiv R A (.cv x) (.cv y)) (synCsn (.cv e))) p0308 p0309
  have p0311 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.imp (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
        (.classEq (synCfpiv R A (.cv x) (.cv y)) (synCsn (.cv e))))
      syntaxFormula0028 p0310
  have p0312 :=
    @gMpdi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classEq (synCfpiv R A (.cv x) (.cv y)) (synCsn (.cv e))) p0181 p0311
  have p0313 := @gEqcom (synCfpiv R A (.cv x) (.cv y)) (synCsn (.cv e))
  have p0314 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (.classEq (synCfpiv R A (.cv x) (.cv y)) (synCsn (.cv e)))
      (.classEq (synCsn (.cv e)) (synCfpiv R A (.cv x) (.cv y))) p0312 p0313
  have p0315 := @gEqeq2 (synCsn (.cv e)) (synCfpiv R A (.cv x) (.cv y)) (.cv q)
  have p0316 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (.classEq (synCsn (.cv e)) (synCfpiv R A (.cv x) (.cv y)))
      (synWb (.classEq (.cv q) (synCsn (.cv e)))
        (.classEq (.cv q) (synCfpiv R A (.cv x) (.cv y))))
      p0314 p0315
  have p0317 :=
    @gBi1 (.classEq (.cv q) (synCsn (.cv e)))
      (.classEq (.cv q) (synCfpiv R A (.cv x) (.cv y)))
  have p0318 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (synWb (.classEq (.cv q) (synCsn (.cv e)))
        (.classEq (.cv q) (synCfpiv R A (.cv x) (.cv y))))
      (.imp (.classEq (.cv q) (synCsn (.cv e)))
        (.classEq (.cv q) (synCfpiv R A (.cv x) (.cv y))))
      p0316 p0317
  have p0319 :=
    @gMpdi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (.classEq (.cv q) (synCsn (.cv e)))
      (.classEq (.cv q) (synCfpiv R A (.cv x) (.cv y))) p0180 p0318
  have p0320 := @gEleq1 (.cv q) (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X)
  have p0321 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (.classEq (.cv q) (synCfpiv R A (.cv x) (.cv y)))
      (synWb (.classMem (.cv q) (synCfdpivrange2 R A X))
        (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X)))
      p0319 p0320
  have p0322 :=
    @gBicom (.classMem (.cv q) (synCfdpivrange2 R A X))
      (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
  have p0323 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (synWb (.classMem (.cv q) (synCfdpivrange2 R A X))
        (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X)))
      (synWb (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
        (.classMem (.cv q) (synCfdpivrange2 R A X)))
      p0321 p0322
  have p0324 :=
    @gBi1 (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
      (.classMem (.cv q) (synCfdpivrange2 R A X))
  have p0325 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (synWb (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
        (.classMem (.cv q) (synCfdpivrange2 R A X)))
      (.imp (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
        (.classMem (.cv q) (synCfdpivrange2 R A X)))
      p0323 p0324
  have p0326 := @gId (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
  have p0327 :=
    @gA1ii
      (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (.imp syntaxFormula0028
          (.imp (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
            (.classMem (.cv q) (synCfdpivrange2 R A X)))))
      (.imp (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
        (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X)))
      p0325 p0326
  have p0328 :=
    @gMpdd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0028
      (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A X))
      (.classMem (.cv q) (synCfdpivrange2 R A X)) p0175 p0327
  have p0329 :=
    @gExp3a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0027
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv q) (synCfdpivrange2 R A X)) p0328
  have p0330 :=
    @gExp3a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0024
      (synWa (.classMem (.cv x) X) (.classMem (.cv y) X)) syntaxFormula0045 p0329
  have p0331 :=
    @gExp4a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0024
      (.classMem (.cv x) X) (.classMem (.cv y) X) syntaxFormula0045 p0330
  have p0332 :=
    @gImp3a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0024
      (.classMem (.cv x) X) syntaxFormula0046 p0331
  have p0333 :=
    @gAlimdv (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0026
      syntaxFormula0046 y dv_cache_0090 p0332
  have p0334 :=
    @gSyl5 syntaxFormula0026 (.all y syntaxFormula0026)
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (.all y syntaxFormula0046)
      p0157 p0333
  have p0335 := (Nominal.biimpRefl syntaxFormula0047)
  have p0336 :=
    @gSyl6ibr (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0026
      (.all y syntaxFormula0046) syntaxFormula0047 p0334 p0335
  have p0337 := @gNfv (.classMem (.cv q) (synCfdpivrange2 R A X)) y dv_cache_0091
  have p0338 :=
    @gR1923 (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv q) (synCfdpivrange2 R A X)) y X p0337
  have p0339 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0026
      syntaxFormula0047 syntaxFormula0048 p0336 p0338
  have p0340 :=
    @gExp3a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0024
      (.classMem (.cv x) X) syntaxFormula0048 p0339
  have p0341 :=
    @gAlimdv (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0024
      syntaxFormula0049 x dv_cache_0092 p0340
  have p0342 :=
    @gSyl5 syntaxFormula0024 (.all x syntaxFormula0024)
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (.all x syntaxFormula0049)
      p0155 p0341
  have p0343 := (Nominal.biimpRefl syntaxFormula0050)
  have p0344 :=
    @gSyl6ibr (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0024
      (.all x syntaxFormula0049) syntaxFormula0050 p0342 p0343
  have p0345 := @gNfv (.classMem (.cv q) (synCfdpivrange2 R A X)) x dv_cache_0093
  have p0346 :=
    @gR1923 (synWrex y X (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv q) (synCfdpivrange2 R A X)) x X p0345
  have p0347 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0024
      syntaxFormula0050
      (.imp syntaxFormula0025 (.classMem (.cv q) (synCfdpivrange2 R A X))) p0344 p0346
  have p0348 :=
    @gMpdi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0024
      syntaxFormula0025 (.classMem (.cv q) (synCfdpivrange2 R A X)) p0153 p0347
  have p0349 :=
    @gExp3a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0023
      (.classEq (.cv q) (synCsn (.cv e))) (.classMem (.cv q) (synCfdpivrange2 R A X))
      p0348
  have p0350 :=
    @gExp3a (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv q) (synCpw1 (synCfdif R A X)))
      (.classMem (.cv e) (synCfdif R A X)) syntaxFormula0051 p0349
  have p0351 :=
    @gAlimdv (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv q) (synCpw1 (synCfdif R A X))) syntaxFormula0052 e dv_cache_0094
      p0350
  have p0352 :=
    @gSyl5 (.classMem (.cv q) (synCpw1 (synCfdif R A X)))
      (.all e (.classMem (.cv q) (synCpw1 (synCfdif R A X))))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (.all e syntaxFormula0052)
      p0145 p0351
  have p0353 := (Nominal.biimpRefl syntaxFormula0053)
  have p0354 :=
    @gSyl6ibr (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv q) (synCpw1 (synCfdif R A X))) (.all e syntaxFormula0052)
      syntaxFormula0053 p0352 p0353
  have p0355 := @gNfv (.classMem (.cv q) (synCfdpivrange2 R A X)) e dv_cache_0095
  have p0356 :=
    @gR1923 (.classEq (.cv q) (synCsn (.cv e)))
      (.classMem (.cv q) (synCfdpivrange2 R A X)) e (synCfdif R A X) p0355
  have p0357 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv q) (synCpw1 (synCfdif R A X))) syntaxFormula0053
      (.imp (synWrex e (synCfdif R A X) (.classEq (.cv q) (synCsn (.cv e))))
        (.classMem (.cv q) (synCfdpivrange2 R A X)))
      p0354 p0356
  have p0358 :=
    @gMpdi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (.cv q) (synCpw1 (synCfdif R A X)))
      (synWrex e (synCfdif R A X) (.classEq (.cv q) (synCsn (.cv e))))
      (.classMem (.cv q) (synCfdpivrange2 R A X)) p0143 p0357
  have p0359 :=
    @gSsrdv (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) q
      (synCpw1 (synCfdif R A X)) (synCfdpivrange2 R A X) dv_cache_0096 dv_cache_0097
      dv_cache_0098 p0358
  have p0360 :=
    @gFdpivrange2ex A X R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0361 := @gNcid (synCfdpivrange2 R A X) p0360
  have p0362 := @gId syntaxFormula0054
  have p0363 := @gPw1exg (synCfdif R A X) (synCvv)
  have p0364 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCfdif R A X) (synCvv))
      (.classMem (synCpw1 (synCfdif R A X)) (synCvv)) p0009 p0363
  have p0365 := @gNcidg (synCpw1 (synCfdif R A X)) (synCvv)
  have p0366 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1 (synCfdif R A X)) (synCvv))
      (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      p0364 p0365
  have p0367 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      syntaxFormula0054 p0366
  have p0368 := @gSseq1 (.cv x) (synCpw1 (synCfdif R A X)) (.cv y)
  have p0369 := @gSseq2 (.cv y) (synCfdpivrange2 R A X) (synCpw1 (synCfdif R A X))
  have p0370 :=
    @gRspc2ev (synWss (.cv x) (.cv y))
      (synWss (synCpw1 (synCfdif R A X)) (synCfdpivrange2 R A X))
      (synWss (synCpw1 (synCfdif R A X)) (.cv y)) x y (synCpw1 (synCfdif R A X))
      (synCfdpivrange2 R A X) (synCnc (synCpw1 (synCfdif R A X)))
      (synCnc (synCfdpivrange2 R A X)) dv_cache_0099 dv_cache_0100 dv_cache_0101
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0008
      p0368 p0369
  have p0371 :=
    @gN3expb
      (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      (.classMem (synCfdpivrange2 R A X) (synCnc (synCfdpivrange2 R A X)))
      (synWss (synCpw1 (synCfdif R A X)) (synCfdpivrange2 R A X)) syntaxFormula0055
      p0370
  have p0372 :=
    @gEx (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      syntaxFormula0054 syntaxFormula0055 p0371
  have p0373 :=
    @gSyl56 syntaxFormula0054 syntaxFormula0054
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      (.imp syntaxFormula0054 syntaxFormula0055) p0362 p0367 p0372
  have p0374 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0054
      syntaxFormula0055 p0373
  have p0375 :=
    @gMpani (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCfdpivrange2 R A X) (synCnc (synCfdpivrange2 R A X)))
      (synWss (synCpw1 (synCfdif R A X)) (synCfdpivrange2 R A X)) syntaxFormula0055
      p0361 p0374
  have p0376 := @gNcex (synCpw1 (synCfdif R A X))
  have p0377 := @gNcex (synCfdpivrange2 R A X)
  have p0378 :=
    @gBrlec x y (synCnc (synCpw1 (synCfdif R A X))) (synCnc (synCfdpivrange2 R A X))
      dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0008 p0376 p0377
  have p0379 :=
    @gSyl6ibr (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWss (synCpw1 (synCfdif R A X)) (synCfdpivrange2 R A X)) syntaxFormula0055
      syntaxFormula0056 p0375 p0378
  have p0380 :=
    @gMpd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWss (synCpw1 (synCfdif R A X)) (synCfdpivrange2 R A X)) syntaxFormula0056
      p0359 p0379
  have p0381 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0056
      (synWwpp) p0380
  have p0382 :=
    @gWppfdpivrangencdlitraw A X R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0383 := @g_pm3_2 syntaxFormula0056 syntaxFormula0057
  have p0384 :=
    @gSyl5 (synWwpp) syntaxFormula0057 syntaxFormula0056 syntaxFormula0058 p0382 p0383
  have p0385 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0056 (.imp (synWwpp) syntaxFormula0058) p0381 p0384
  have p0386 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0058 p0385
  have p0388 := @gNcelncs (synCfdpivrange2 R A X) (synCvv)
  have p0389 := Nominal.mp p0360 p0388
  have p0390 := @gXpkex X X hyp_cfbfdwppcarrierimpndv_3 hyp_cfbfdwppcarrierimpndv_3
  have p0391 := @gNncex
  have p0392 := @gXpex (synCxpk X X) (synCnnc) p0390 p0391
  have p0393 := @gNcelncs (synCxp (synCxpk X X) (synCnnc)) (synCvv)
  have p0394 := Nominal.mp p0392 p0393
  have p0395 := @gNcelncs (synCpw1 (synCfdif R A X)) (synCvv)
  have p0396 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1 (synCfdif R A X)) (synCvv))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs)) p0364 p0395
  have p0397 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs)) syntaxFormula0059
      p0396
  have p0398 := Nominal.ax1 syntaxFormula0059 syntaxFormula0059
  have p0399 := Nominal.ax1 syntaxFormula0059 syntaxFormula0060
  have p0400 := @gMpd syntaxFormula0059 syntaxFormula0060 syntaxFormula0059 p0398 p0399
  have p0401 :=
    @gA1i syntaxFormula0060 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      p0400
  have p0402 :=
    @gLectr (synCnc (synCpw1 (synCfdif R A X))) (synCnc (synCfdpivrange2 R A X))
      (synCnc (synCxp (synCxpk X X) (synCnnc)))
  have p0403 :=
    @gN3expb (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs))
      (.classMem (synCnc (synCfdpivrange2 R A X)) (synCncs))
      (.classMem (synCnc (synCxp (synCxpk X X) (synCnnc))) (synCncs))
      syntaxFormula0062 p0402
  have p0404 :=
    @gEx (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs)) syntaxFormula0059
      syntaxFormula0062 p0403
  have p0405 :=
    @gSyl6c (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0059
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs)) syntaxFormula0059
      syntaxFormula0062 p0397 p0401 p0404
  have p0406 :=
    @gMp2ani (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCfdpivrange2 R A X)) (synCncs))
      (.classMem (synCnc (synCxp (synCxpk X X) (synCnnc))) (synCncs))
      syntaxFormula0062 p0389 p0394 p0405
  have p0407 :=
    @gSyld (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0058 syntaxFormula0061 p0386 p0406
  have p0413 :=
    @gJctir (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs))
      (.classMem (synCnc (synCxp (synCxpk X X) (synCnnc))) (synCncs)) p0396 p0394
  have p0414 :=
    @gTlecg (synCnc (synCpw1 (synCfdif R A X)))
      (synCnc (synCxp (synCxpk X X) (synCnnc)))
  have p0415 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs))
        (.classMem (synCnc (synCxp (synCxpk X X) (synCnnc))) (synCncs)))
      (synWb syntaxFormula0061 syntaxFormula0063) p0413 p0414
  have p0416 :=
    @gSylibd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0061 syntaxFormula0063 p0407 p0415
  have p0417 := @gTccl (synCnc (synCpw1 (synCfdif R A X)))
  have p0418 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs))
      (.classMem (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synCncs)) p0396 p0417
  have p0424 := @gTccl (synCnc (synCxp (synCxpk X X) (synCnnc)))
  have p0425 := Nominal.mp p0394 p0424
  have p0426 :=
    @gJctir (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synCncs))
      (.classMem (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc)))) (synCncs)) p0418
      p0425
  have p0427 :=
    @gTlecg (synCtc (synCnc (synCpw1 (synCfdif R A X))))
      (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc))))
  have p0428 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa (.classMem (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synCncs))
        (.classMem (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc)))) (synCncs)))
      (synWb syntaxFormula0063 syntaxFormula0064) p0426 p0427
  have p0429 :=
    @gSylibd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0063 syntaxFormula0064 p0416 p0428
  have p0430 :=
    @gFdordwe2 A X R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_cfbfdwppcarrierimpndv_1 hyp_cfbfdwppcarrierimpndv_2 hyp_cfbfdwppcarrierimpndv_3
  have p0431 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWbr R (synCwe) A) (synWbr (synCfdord R A X) (synCwe) (synCfdif R A X))
      p0003 p0430
  have p0432 := @gSiwendv (synCfdif R A X) (synCfdord R A X)
  have p0433 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWbr (synCfdord R A X) (synCwe) (synCfdif R A X))
      (synWbr (synCsi (synCfdord R A X)) (synCwe) (synCpw1 (synCfdif R A X))) p0431
      p0432
  have p0434 :=
    @gNcwehwcardsndv (synCpw1 (synCfdif R A X)) (synCsi (synCfdord R A X))
  have p0435 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWbr (synCsi (synCfdord R A X)) (synCwe) (synCpw1 (synCfdif R A X)))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synChwcards (synCvv))) p0433
      p0434
  have p0436 := @gHwcardstcclndv (synCnc (synCpw1 (synCfdif R A X)))
  have p0437 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synChwcards (synCvv)))
      (.classMem (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synChwcards (synCvv)))
      p0435 p0436
  have p0438 := @gHwcardstcclndv (synCtc (synCnc (synCpw1 (synCfdif R A X))))
  have p0439 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synChwcards (synCvv)))
      syntaxFormula0065 p0437 p0438
  have p0443 := @gHncardhwcardsndv (synCxp (synCxpk X X) (synCnnc))
  have p0444 := Nominal.mp p0392 p0443
  have p0445 :=
    @gJctir (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0065
      (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc))) (synChwcards (synCvv)))
      p0439 p0444
  have p0446 :=
    @gHwcardslecconnexndv (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X)))))
      (synChncard (synCxp (synCxpk X X) (synCnnc)))
  have p0447 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa syntaxFormula0065 (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc)))
          (synChwcards (synCvv))))
      syntaxFormula0068 p0445 p0446
  have p0448 := @gPm253 syntaxFormula0066 syntaxFormula0067
  have p0449 := @gHncardtc2nodomndv (synCxp (synCxpk X X) (synCnnc)) p0392
  have p0450 := @gNotnot2 syntaxFormula0067
  have p0455 := @gTccl (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc))))
  have p0456 := Nominal.mp p0425 p0455
  have p0457 := @gHwcardssnc (synCvv)
  have p0458 :=
    @gSseldi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synChwcards (synCvv)) (synCncs)
      (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X))))) p0457 p0439
  have p0459 := @gHncardnc (synCxp (synCxpk X X) (synCnnc))
  have p0460 := Nominal.mp p0392 p0459
  have p0461 :=
    @gJctil (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0069
      (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc))) (synCncs)) p0458 p0460
  have p0462 :=
    @gBiantrurd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc))) (synCncs))
        syntaxFormula0069)
      syntaxFormula0070 p0461
  have p0463 := (Nominal.biimpRefl syntaxFormula0071)
  have p0464 :=
    @gSyl6rbbr (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0070
      (synWa (synWa (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc))) (synCncs))
          syntaxFormula0069) syntaxFormula0070)
      syntaxFormula0071 p0462 p0463
  have p0465 :=
    @gMpbiri (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0071
      syntaxFormula0070 p0456 p0464
  have p0466 :=
    @gLectr (synChncard (synCxp (synCxpk X X) (synCnnc)))
      (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X)))))
      (synCtc (synCtc (synCnc (synCxp (synCxpk X X) (synCnnc)))))
  have p0467 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0071
      (.imp (synWa syntaxFormula0067 syntaxFormula0064) syntaxFormula0072) p0465 p0466
  have p0468 :=
    @gExp3acom23 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      syntaxFormula0067 syntaxFormula0064 syntaxFormula0072 p0467
  have p0469 :=
    @gSyl7 syntaxFormula0074 syntaxFormula0067
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0064
      syntaxFormula0072 p0450 p0468
  have p0470 := @gNotnot1 syntaxFormula0072
  have p0471 :=
    @gSyl8 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0064
      syntaxFormula0074 syntaxFormula0072 (.neg syntaxFormula0075) p0469 p0470
  have p0472 := Nominal.ax3 syntaxFormula0073 syntaxFormula0075
  have p0473 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0064
      (.imp syntaxFormula0074 (.neg syntaxFormula0075))
      (.imp syntaxFormula0075 syntaxFormula0073) p0471 p0472
  have p0474 :=
    @gMpii (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0064
      syntaxFormula0075 syntaxFormula0073 p0449 p0473
  have p0475 :=
    @gA1dd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0064
      syntaxFormula0073 syntaxFormula0076 p0474
  have p0476 := Nominal.ax3 syntaxFormula0066 syntaxFormula0067
  have p0477 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0064
      (.imp syntaxFormula0076 syntaxFormula0073)
      (.imp syntaxFormula0067 syntaxFormula0066) p0475 p0476
  have p0478 :=
    @gCom23 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0064
      syntaxFormula0067 syntaxFormula0066 p0477
  have p0479 :=
    @gSyl9r syntaxFormula0068 syntaxFormula0076 syntaxFormula0067
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0077 p0448
      p0478
  have p0480 := @gNotnot1 syntaxFormula0077
  have p0481 :=
    @gSyl8 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0068
      syntaxFormula0076 syntaxFormula0077 syntaxFormula0079 p0479 p0480
  have p0482 := Nominal.ax3 syntaxFormula0066 syntaxFormula0078
  have p0483 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0068
      (.imp syntaxFormula0076 syntaxFormula0079) syntaxFormula0080 p0481 p0482
  have p0484 := @gIdd syntaxFormula0064 syntaxFormula0066
  have p0485 := @gCom12 syntaxFormula0064 syntaxFormula0066 syntaxFormula0066 p0484
  have p0486 := @gA1i syntaxFormula0081 syntaxFormula0068 p0485
  have p0487 := @gA1d syntaxFormula0068 syntaxFormula0081 syntaxFormula0078 p0486
  have p0488 :=
    @gA2d syntaxFormula0068 syntaxFormula0078 syntaxFormula0066 syntaxFormula0077 p0487
  have p0489 :=
    @gSylcom (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0068
      syntaxFormula0080 syntaxFormula0082 p0483 p0488
  have p0490 := @gPm218 syntaxFormula0077
  have p0491 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0068
      syntaxFormula0082 syntaxFormula0077 p0489 p0490
  have p0492 :=
    @gCom23 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0068
      syntaxFormula0064 syntaxFormula0066 p0491
  have p0493 :=
    @gMpid (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0064
      syntaxFormula0068 syntaxFormula0066 p0447 p0492
  have p0494 :=
    @gSyld (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0064 syntaxFormula0066 p0429 p0493
  have p0495 := @gA1i syntaxFormula0083 (synWwpp) hyp_cfbfdwppcarrierimpndv_4
  have p0496 := @g_pm3_2 syntaxFormula0066 syntaxFormula0083
  have p0497 :=
    @gSyl5 (synWwpp) syntaxFormula0083 syntaxFormula0066 syntaxFormula0084 p0495 p0496
  have p0498 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0066 (.imp (synWwpp) syntaxFormula0084) p0494 p0497
  have p0499 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0084 p0498
  have p0505 := @gHncardnc X
  have p0506 := Nominal.mp hyp_cfbfdwppcarrierimpndv_3 p0505
  have p0507 := @gTccl (synChncard X)
  have p0508 := Nominal.mp p0506 p0507
  have p0509 := @gTccl (synCtc (synChncard X))
  have p0510 := Nominal.mp p0508 p0509
  have p0511 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0069
      syntaxFormula0085 p0458
  have p0512 := Nominal.ax1 syntaxFormula0085 syntaxFormula0085
  have p0513 := Nominal.ax1 syntaxFormula0085 syntaxFormula0086
  have p0514 := @gMpd syntaxFormula0085 syntaxFormula0086 syntaxFormula0085 p0512 p0513
  have p0515 :=
    @gA1i syntaxFormula0086 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      p0514
  have p0516 :=
    @gLectr (synCtc (synCtc (synCnc (synCpw1 (synCfdif R A X)))))
      (synChncard (synCxp (synCxpk X X) (synCnnc)))
      (synCtc (synCtc (synChncard X)))
  have p0517 :=
    @gN3expb syntaxFormula0069
      (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc))) (synCncs))
      (.classMem (synCtc (synCtc (synChncard X))) (synCncs)) syntaxFormula0088 p0516
  have p0518 := @gEx syntaxFormula0069 syntaxFormula0085 syntaxFormula0088 p0517
  have p0519 :=
    @gSyl6c (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0085
      syntaxFormula0069 syntaxFormula0085 syntaxFormula0088 p0511 p0515 p0518
  have p0520 :=
    @gMp2ani (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synChncard (synCxp (synCxpk X X) (synCnnc))) (synCncs))
      (.classMem (synCtc (synCtc (synChncard X))) (synCncs)) syntaxFormula0088 p0460
      p0510 p0519
  have p0521 :=
    @gSyld (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0084 syntaxFormula0087 p0499 p0520
  have p0526 :=
    @gJctir (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synCncs))
      (.classMem (synCtc (synChncard X)) (synCncs)) p0418 p0508
  have p0527 :=
    @gTlecg (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synCtc (synChncard X))
  have p0528 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa (.classMem (synCtc (synCnc (synCpw1 (synCfdif R A X)))) (synCncs))
        (.classMem (synCtc (synChncard X)) (synCncs)))
      (synWb syntaxFormula0089 syntaxFormula0087) p0526 p0527
  have p0529 :=
    @gSylibrd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0087 syntaxFormula0089 p0521 p0528
  have p0532 :=
    @gJctir (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs))
      (.classMem (synChncard X) (synCncs)) p0396 p0506
  have p0533 := @gTlecg (synCnc (synCpw1 (synCfdif R A X))) (synChncard X)
  have p0534 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWa (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs))
        (.classMem (synChncard X) (synCncs)))
      (synWb (synWbr (synCnc (synCpw1 (synCfdif R A X))) (synClec) (synChncard X))
        syntaxFormula0089)
      p0532 p0533
  have p0535 :=
    @gSylibrd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0089
      (synWbr (synCnc (synCpw1 (synCfdif R A X))) (synClec) (synChncard X)) p0529
      p0534
  have p0536 := (Nominal.classEqRefl (synChncard X))
  have p0537 :=
    @gBreq2i (synChncard X) (synCnc (synChnord X))
      (synCnc (synCpw1 (synCfdif R A X))) (synClec) p0536
  have p0538 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      (synWbr (synCnc (synCpw1 (synCfdif R A X))) (synClec) (synChncard X))
      syntaxFormula0090 p0535 p0537
  have p0539 := @gHnordex X hyp_cfbfdwppcarrierimpndv_3
  have p0540 := @gNcelncsi (synChnord X) p0539
  have p0541 :=
    @gDflec3 g (synCnc (synCpw1 (synCfdif R A X))) (synCnc (synChnord X)) p q
      dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112
  have p0542 :=
    @gSylancl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs))
      (.classMem (synCnc (synChnord X)) (synCncs))
      (synWb syntaxFormula0090 (synWrex p (synCnc (synCpw1 (synCfdif R A X)))
          (synWrex q (synCnc (synChnord X)) (synWex g (synWf1 (.cv g) (.cv p) (.cv q))))))
      p0396 p0540 p0541
  have p0543 := @gElnc (.cv p) (synCpw1 (synCfdif R A X))
  have p0544 := @gBren (.cv p) (synCpw1 (synCfdif R A X)) h dv_cache_0113 dv_cache_0114
  have p0545 :=
    @gBitri (.classMem (.cv p) (synCnc (synCpw1 (synCfdif R A X))))
      (synWbr (.cv p) (synCen) (synCpw1 (synCfdif R A X)))
      (synWex h (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))) p0543 p0544
  have p0546 := @gElnc (.cv q) (synChnord X)
  have p0547 := @gBren (.cv q) (synChnord X) i dv_cache_0115 dv_cache_0116
  have p0548 :=
    @gBitri (.classMem (.cv q) (synCnc (synChnord X)))
      (synWbr (.cv q) (synCen) (synChnord X))
      (synWex i (synWf1o (.cv i) (.cv q) (synChnord X))) p0546 p0547
  have p0549 :=
    @gAnbi12i (.classMem (.cv p) (synCnc (synCpw1 (synCfdif R A X))))
      (synWex h (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X))))
      (.classMem (.cv q) (synCnc (synChnord X)))
      (synWex i (synWf1o (.cv i) (.cv q) (synChnord X))) p0545 p0548
  have p0550 :=
    @gEeanv (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))
      (synWf1o (.cv i) (.cv q) (synChnord X)) h i dv_cache_0117 dv_cache_0118
  have p0551 :=
    @gBitr4i syntaxFormula0091
      (synWa (synWex h (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X))))
        (synWex i (synWf1o (.cv i) (.cv q) (synChnord X))))
      (synWex h (synWex i syntaxFormula0092)) p0549 p0550
  have p0552 := @gF1of1 (.cv q) (synChnord X) (.cv i)
  have p0553 :=
    @gN3ad2ant2 (synWf1o (.cv i) (.cv q) (synChnord X))
      (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))
      (synWf1 (.cv i) (.cv q) (synChnord X)) (synWf1 (.cv g) (.cv p) (.cv q)) p0552
  have p0554 :=
    @gSimp3 (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))
      (synWf1o (.cv i) (.cv q) (synChnord X)) (synWf1 (.cv g) (.cv p) (.cv q))
  have p0555 := @gF1co (.cv p) (.cv q) (synChnord X) (.cv i) (.cv g)
  have p0556 :=
    @gSyl2anc syntaxFormula0093 (synWf1 (.cv i) (.cv q) (synChnord X))
      (synWf1 (.cv g) (.cv p) (.cv q))
      (synWf1 (synCcom (.cv i) (.cv g)) (.cv p) (synChnord X)) p0553 p0554 p0555
  have p0557 := @gF1ocnv (.cv p) (synCpw1 (synCfdif R A X)) (.cv h)
  have p0558 := @gF1of1 (synCpw1 (synCfdif R A X)) (.cv p) (synCcnv (.cv h))
  have p0559 :=
    @gSyl (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))
      (synWf1o (synCcnv (.cv h)) (synCpw1 (synCfdif R A X)) (.cv p))
      (synWf1 (synCcnv (.cv h)) (synCpw1 (synCfdif R A X)) (.cv p)) p0557 p0558
  have p0560 :=
    @gN3ad2ant1 (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))
      (synWf1o (.cv i) (.cv q) (synChnord X))
      (synWf1 (synCcnv (.cv h)) (synCpw1 (synCfdif R A X)) (.cv p))
      (synWf1 (.cv g) (.cv p) (.cv q)) p0559
  have p0561 :=
    @gF1co (synCpw1 (synCfdif R A X)) (.cv p) (synChnord X) (synCcom (.cv i) (.cv g))
      (synCcnv (.cv h))
  have p0562 :=
    @gSyl2anc syntaxFormula0093
      (synWf1 (synCcom (.cv i) (.cv g)) (.cv p) (synChnord X))
      (synWf1 (synCcnv (.cv h)) (synCpw1 (synCfdif R A X)) (.cv p)) syntaxFormula0094
      p0556 p0560 p0561
  have p0563 := @gVex i
  have p0564 := @gVex g
  have p0565 := @gCoex (.cv i) (.cv g) p0563 p0564
  have p0566 := @gVex h
  have p0567 := @gCnvex (.cv h) p0566
  have p0568 := @gCoex (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)) p0565 p0567
  have p0569 :=
    @gF1eq1 (synCpw1 (synCfdif R A X)) (synChnord X) (.cv f)
      (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)))
  have p0570 :=
    @gSpcev (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))
      syntaxFormula0094 f (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv h)))
      dv_cache_0119 dv_cache_0120 p0568 p0569
  have p0571 :=
    @gSyl syntaxFormula0093 syntaxFormula0094
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))) p0562
      p0570
  have p0572 :=
    @gN3expia (synWf1o (.cv h) (.cv p) (synCpw1 (synCfdif R A X)))
      (synWf1o (.cv i) (.cv q) (synChnord X)) (synWf1 (.cv g) (.cv p) (.cv q))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))) p0571
  have p0573 :=
    @gExlimivv syntaxFormula0092
      (.imp (synWf1 (.cv g) (.cv p) (.cv q))
        (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))))
      h i dv_cache_0121 dv_cache_0122 p0572
  have p0574 :=
    @gSylbi syntaxFormula0091 (synWex h (synWex i syntaxFormula0092))
      (.imp (synWf1 (.cv g) (.cv p) (.cv q))
        (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))))
      p0551 p0573
  have p0575 :=
    @gExlimdv syntaxFormula0091 (synWf1 (.cv g) (.cv p) (.cv q))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))) g
      dv_cache_0123 dv_cache_0124 p0574
  have p0576 :=
    @gRexlimivv (synWex g (synWf1 (.cv g) (.cv p) (.cv q)))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))) p q
      (synCnc (synCpw1 (synCfdif R A X))) (synCnc (synChnord X)) dv_cache_0125
      dv_cache_0126 dv_cache_0127 dv_cache_0110 p0575
  have p0577 :=
    @gSyl6bi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0090
      (synWrex p (synCnc (synCpw1 (synCfdif R A X))) (synWrex q (synCnc (synChnord X))
          (synWex g (synWf1 (.cv g) (.cv p) (.cv q)))))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))) p0542
      p0576
  have p0578 := @gNcid (synChnord X) p0539
  have p0579 := @gId syntaxFormula0095
  have p0580 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      syntaxFormula0095 p0366
  have p0581 := @gF1eq2 (.cv a) (synCpw1 (synCfdif R A X)) (.cv b) (.cv f)
  have p0582 :=
    @gExbidv (.classEq (.cv a) (synCpw1 (synCfdif R A X)))
      (synWf1 (.cv f) (.cv a) (.cv b))
      (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (.cv b)) f dv_cache_0128 p0581
  have p0583 := @gF1eq3 (.cv b) (synChnord X) (synCpw1 (synCfdif R A X)) (.cv f)
  have p0584 :=
    @gExbidv (.classEq (.cv b) (synChnord X))
      (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (.cv b))
      (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)) f dv_cache_0129 p0583
  have p0585 :=
    @gRspc2ev (synWex f (synWf1 (.cv f) (.cv a) (.cv b)))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (.cv b))) a b
      (synCpw1 (synCfdif R A X)) (synChnord X) (synCnc (synCpw1 (synCfdif R A X)))
      (synCnc (synChnord X)) dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133
      dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0075 p0582 p0584
  have p0586 :=
    @gN3expb
      (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      (.classMem (synChnord X) (synCnc (synChnord X)))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))
      syntaxFormula0097 p0585
  have p0587 :=
    @gEx (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      syntaxFormula0095 syntaxFormula0097 p0586
  have p0588 :=
    @gSyl56 syntaxFormula0095 syntaxFormula0095
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1 (synCfdif R A X)) (synCnc (synCpw1 (synCfdif R A X))))
      (.imp syntaxFormula0095 syntaxFormula0097) p0579 p0580 p0587
  have p0589 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0095
      syntaxFormula0097 p0588
  have p0590 :=
    @gMpani (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synChnord X) (synCnc (synChnord X)))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))
      syntaxFormula0097 p0578 p0589
  have p0591 :=
    @gDflec3 f (synCnc (synCpw1 (synCfdif R A X))) (synCnc (synChnord X)) a b
      dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0075 dv_cache_0138 dv_cache_0139
  have p0592 :=
    @gSylancl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCnc (synCpw1 (synCfdif R A X))) (synCncs))
      (.classMem (synCnc (synChnord X)) (synCncs))
      (synWb syntaxFormula0090 syntaxFormula0097) p0396 p0540 p0591
  have p0593 :=
    @gSylibrd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))
      syntaxFormula0097 syntaxFormula0090 p0590 p0592
  have p0594 :=
    @gImpbid (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0090
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))) p0577
      p0593
  have p0595 :=
    @gSylibd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0090
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X))) p0538
      p0594
  have p0596 :=
    @gSyld (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))
      syntaxFormula0090 p0595 p0593
  have p0597 :=
    @gF1pw2exim (synCpw1 (synCfdif R A X)) (synChnord X) f h dv_cache_0140
      dv_cache_0114 dv_cache_0141 dv_cache_0142 dv_cache_0143
  have p0598 :=
    @gSyl6 (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0090
      (synWex f (synWf1 (.cv f) (synCpw1 (synCfdif R A X)) (synChnord X)))
      syntaxFormula0099 p0577 p0597
  have p0599 := @gPwexg (synCpw1 (synCfdif R A X)) (synCvv)
  have p0600 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw1 (synCfdif R A X)) (synCvv))
      (.classMem (synCpw (synCpw1 (synCfdif R A X))) (synCvv)) p0364 p0599
  have p0601 := @gPwexg (synCpw (synCpw1 (synCfdif R A X))) (synCvv)
  have p0602 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw (synCpw1 (synCfdif R A X))) (synCvv))
      (.classMem (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (synCvv)) p0600 p0601
  have p0603 := @gNcelncs (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (synCvv)
  have p0604 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (synCvv))
      syntaxFormula0100 p0602 p0603
  have p0606 := @gPwex (synChnord X) p0539
  have p0607 := @gPwex (synCpw (synChnord X)) p0606
  have p0608 := @gNcelncsi (synCpw (synCpw (synChnord X))) p0607
  have p0609 :=
    @gDflec3 g (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synCnc (synCpw (synCpw (synChnord X)))) p q dv_cache_0144 dv_cache_0145
      dv_cache_0146 dv_cache_0110 dv_cache_0111 dv_cache_0112
  have p0610 :=
    @gSylancl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0100
      (.classMem (synCnc (synCpw (synCpw (synChnord X)))) (synCncs))
      (synWb syntaxFormula0101 syntaxFormula0102) p0604 p0608 p0609
  have p0611 := @gElnc (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X))))
  have p0612 :=
    @gBren (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) a dv_cache_0147
      dv_cache_0148
  have p0613 :=
    @gBitri
      (.classMem (.cv p) (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
      (synWbr (.cv p) (synCen) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWex a (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
      p0611 p0612
  have p0614 := @gElnc (.cv q) (synCpw (synCpw (synChnord X)))
  have p0615 :=
    @gBren (.cv q) (synCpw (synCpw (synChnord X))) i dv_cache_0115 dv_cache_0149
  have p0616 :=
    @gBitri (.classMem (.cv q) (synCnc (synCpw (synCpw (synChnord X)))))
      (synWbr (.cv q) (synCen) (synCpw (synCpw (synChnord X))))
      (synWex i (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))) p0614
      p0615
  have p0617 :=
    @gAnbi12i
      (.classMem (.cv p) (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
      (synWex a (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
      (.classMem (.cv q) (synCnc (synCpw (synCpw (synChnord X)))))
      (synWex i (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))) p0613
      p0616
  have p0618 :=
    @gEeanv (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X)))) a i dv_cache_0150
      dv_cache_0151
  have p0619 :=
    @gBitr4i syntaxFormula0103
      (synWa (synWex a
          (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X))))))
        (synWex i (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))))
      syntaxFormula0105 p0617 p0618
  have p0620 := @gF1of1 (.cv q) (synCpw (synCpw (synChnord X))) (.cv i)
  have p0621 :=
    @gN3ad2ant2 (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))
      (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1 (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv g) (.cv p) (.cv q)) p0620
  have p0622 :=
    @gSimp3 (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv g) (.cv p) (.cv q))
  have p0623 := @gF1co (.cv p) (.cv q) (synCpw (synCpw (synChnord X))) (.cv i) (.cv g)
  have p0624 :=
    @gSyl2anc syntaxFormula0106
      (synWf1 (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv g) (.cv p) (.cv q))
      (synWf1 (synCcom (.cv i) (.cv g)) (.cv p) (synCpw (synCpw (synChnord X))))
      p0621 p0622 p0623
  have p0625 := @gF1ocnv (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv a)
  have p0626 :=
    @gF1of1 (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv p) (synCcnv (.cv a))
  have p0627 :=
    @gSyl (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1o (synCcnv (.cv a)) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv p))
      (synWf1 (synCcnv (.cv a)) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv p))
      p0625 p0626
  have p0628 :=
    @gN3ad2ant1
      (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))
      (synWf1 (synCcnv (.cv a)) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv p))
      (synWf1 (.cv g) (.cv p) (.cv q)) p0627
  have p0629 :=
    @gF1co (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv p)
      (synCpw (synCpw (synChnord X))) (synCcom (.cv i) (.cv g)) (synCcnv (.cv a))
  have p0630 :=
    @gSyl2anc syntaxFormula0106
      (synWf1 (synCcom (.cv i) (.cv g)) (.cv p) (synCpw (synCpw (synChnord X))))
      (synWf1 (synCcnv (.cv a)) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv p))
      syntaxFormula0107 p0624 p0628 p0629
  have p0634 := @gVex a
  have p0635 := @gCnvex (.cv a) p0634
  have p0636 := @gCoex (synCcom (.cv i) (.cv g)) (synCcnv (.cv a)) p0565 p0635
  have p0637 :=
    @gF1eq1 (synCpw (synCpw (synCpw1 (synCfdif R A X))))
      (synCpw (synCpw (synChnord X))) (.cv h)
      (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv a)))
  have p0638 :=
    @gSpcev syntaxFormula0098 syntaxFormula0107 h
      (synCcom (synCcom (.cv i) (.cv g)) (synCcnv (.cv a))) dv_cache_0152 dv_cache_0153
      p0636 p0637
  have p0639 := @gSyl syntaxFormula0106 syntaxFormula0107 syntaxFormula0099 p0630 p0638
  have p0640 :=
    @gN3expia
      (synWf1o (.cv a) (.cv p) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1o (.cv i) (.cv q) (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv g) (.cv p) (.cv q)) syntaxFormula0099 p0639
  have p0641 :=
    @gExlimivv syntaxFormula0104
      (.imp (synWf1 (.cv g) (.cv p) (.cv q)) syntaxFormula0099) a i dv_cache_0154
      dv_cache_0155 p0640
  have p0642 :=
    @gSylbi syntaxFormula0103 syntaxFormula0105
      (.imp (synWf1 (.cv g) (.cv p) (.cv q)) syntaxFormula0099) p0619 p0641
  have p0643 :=
    @gExlimdv syntaxFormula0103 (synWf1 (.cv g) (.cv p) (.cv q)) syntaxFormula0099 g
      dv_cache_0156 dv_cache_0157 p0642
  have p0644 :=
    @gRexlimivv (synWex g (synWf1 (.cv g) (.cv p) (.cv q))) syntaxFormula0099 p q
      (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synCnc (synCpw (synCpw (synChnord X)))) dv_cache_0158 dv_cache_0159
      dv_cache_0160 dv_cache_0110 p0643
  have p0645 :=
    @gSyl6bi (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0101
      syntaxFormula0102 syntaxFormula0099 p0610 p0644
  have p0646 := @gNcid (synCpw (synCpw (synChnord X))) p0607
  have p0647 := @gId syntaxFormula0109
  have p0648 := @gNcidg (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (synCvv)
  have p0649 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X)))
      (.classMem (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (synCvv))
      syntaxFormula0110 p0602 p0648
  have p0650 :=
    @gA1d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0110
      syntaxFormula0109 p0649
  have p0651 :=
    @gF1eq2 (.cv b) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv c) (.cv h)
  have p0652 :=
    @gExbidv (.classEq (.cv b) (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synWf1 (.cv h) (.cv b) (.cv c))
      (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv c)) h
      dv_cache_0161 p0651
  have p0653 :=
    @gF1eq3 (.cv c) (synCpw (synCpw (synChnord X)))
      (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv h)
  have p0654 :=
    @gExbidv (.classEq (.cv c) (synCpw (synCpw (synChnord X))))
      (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv c))
      syntaxFormula0098 h dv_cache_0162 p0653
  have p0655 :=
    @gRspc2ev (synWex h (synWf1 (.cv h) (.cv b) (.cv c))) syntaxFormula0099
      (synWex h (synWf1 (.cv h) (synCpw (synCpw (synCpw1 (synCfdif R A X)))) (.cv c)))
      b c (synCpw (synCpw (synCpw1 (synCfdif R A X))))
      (synCpw (synCpw (synChnord X)))
      (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synCnc (synCpw (synCpw (synChnord X)))) dv_cache_0163 dv_cache_0164
      dv_cache_0165 dv_cache_0166 dv_cache_0167 dv_cache_0168 dv_cache_0169 dv_cache_0170
      dv_cache_0171 p0652 p0654
  have p0656 :=
    @gN3expb syntaxFormula0110 syntaxFormula0108 syntaxFormula0099 syntaxFormula0112
      p0655
  have p0657 := @gEx syntaxFormula0110 syntaxFormula0109 syntaxFormula0112 p0656
  have p0658 :=
    @gSyl56 syntaxFormula0109 syntaxFormula0109
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0110
      (.imp syntaxFormula0109 syntaxFormula0112) p0647 p0650 p0657
  have p0659 :=
    @gPm243d (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0109
      syntaxFormula0112 p0658
  have p0660 :=
    @gMpani (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0108
      syntaxFormula0099 syntaxFormula0112 p0646 p0659
  have p0661 :=
    @gDflec3 h (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synCnc (synCpw (synCpw (synChnord X)))) b c dv_cache_0166 dv_cache_0167
      dv_cache_0168 dv_cache_0171 dv_cache_0172 dv_cache_0173
  have p0662 :=
    @gSylancl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0100
      (.classMem (synCnc (synCpw (synCpw (synChnord X)))) (synCncs))
      (synWb syntaxFormula0101 syntaxFormula0112) p0604 p0608 p0661
  have p0663 :=
    @gSylibrd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0099
      syntaxFormula0112 syntaxFormula0101 p0660 p0662
  have p0664 :=
    @gImpbid (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0101
      syntaxFormula0099 p0645 p0663
  have p0665 :=
    @gBiimprd (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0101
      syntaxFormula0099 p0664
  have p0666 :=
    @gSyld (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0090
      syntaxFormula0099 syntaxFormula0101 p0598 p0665
  have p0667 :=
    @gSyld (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0090 syntaxFormula0101 p0596 p0666
  have p0668 :=
    @gJcad (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0022 syntaxFormula0101 p0141 p0667
  have p0672 := @gNcelncs (synCpw (synCpw (synChnord X))) (synCvv)
  have p0673 := Nominal.mp p0607 p0672
  have p0680 := @gTccl (synCtc (synCtc (synCnc A)))
  have p0681 := Nominal.mp p0021 p0680
  have p0682 :=
    @gLectr (synCtc (synCtc (synCtc (synCnc A))))
      (synCnc (synCpw (synCpw (synCpw1 (synCfdif R A X)))))
      (synCnc (synCpw (synCpw (synChnord X))))
  have p0683 :=
    @gMp3an1 (.classMem (synCtc (synCtc (synCtc (synCnc A)))) (synCncs))
      syntaxFormula0100
      (.classMem (synCnc (synCpw (synCpw (synChnord X)))) (synCncs))
      syntaxFormula0115 p0681 p0682
  have p0684 :=
    @gSylancl (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) syntaxFormula0100
      (.classMem (synCnc (synCpw (synCpw (synChnord X)))) (synCncs))
      syntaxFormula0115 p0604 p0673 p0683
  have p0685 :=
    @gSyld (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0113 syntaxFormula0114 p0668 p0684
  have p0686 := @gTc3nc A hyp_cfbfdwppcarrierimpndv_2
  have p0687 :=
    @gBreq1i (synCtc (synCtc (synCtc (synCnc A))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 A))))
      (synCnc (synCpw (synCpw (synChnord X)))) (synClec) p0686
  have p0688 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      syntaxFormula0114
      (synWbr (synCnc (synCpw1 (synCpw1 (synCpw1 A)))) (synClec)
        (synCnc (synCpw (synCpw (synChnord X)))))
      p0685 p0687
  have p0689 := @gPw1ex A hyp_cfbfdwppcarrierimpndv_2
  have p0690 := @gPw1ex (synCpw1 A) p0689
  have p0691 := @gPw1ex (synCpw1 (synCpw1 A)) p0690
  have p0695 :=
    @gNclenc (synCpw1 (synCpw1 (synCpw1 A))) (synCpw (synCpw (synChnord X))) k
      dv_cache_0174 dv_cache_0175 p0691 p0607
  have p0696 :=
    @gSyl6ib (synWa (synWbr R (synCwe) A) (synWss A (synCpw X))) (synWwpp)
      (synWbr (synCnc (synCpw1 (synCpw1 (synCpw1 A)))) (synClec)
        (synCnc (synCpw (synCpw (synChnord X)))))
      (synWex k (synWf1 (.cv k) (synCpw1 (synCpw1 (synCpw1 A)))
          (synCpw (synCpw (synChnord X)))))
      p0688 p0695
  exact p0696


end NFChoice.DirectNominalPrf.WPPReplay
