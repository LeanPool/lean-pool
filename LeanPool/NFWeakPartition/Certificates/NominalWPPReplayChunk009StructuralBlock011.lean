/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart051`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ncfinlower (A : Class) (B : Class) (n : Var) (M : Class)
    (dv_A_n : n ∉ A.fv) (dv_B_n : n ∉ B.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 A) M)
          (.classMem (syn_cpw1 B) M))
        (syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({ n } : Finset Var) ∪ M.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  let c : Var := freshVar proofSupport 4
  let x : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  let y : Var := freshVar proofSupport 7
  let e : Var := freshVar proofSupport 8
  let z : Var := freshVar proofSupport 9
  let f : Var := freshVar proofSupport 10
  let w : Var := freshVar proofSupport 11
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_b : n ≠ b := Ne.symm fresh_b_ne_n
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_m : n ≠ m := Ne.symm fresh_m_ne_n
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_ne_n : k ≠ n := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_k : n ≠ k := Ne.symm fresh_k_ne_n
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_c_ne_n : c ≠ n := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_e_ne_n : e ≠ n := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_e : n ≠ e := Ne.symm fresh_e_ne_n
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 9 ∉ proofSupport
    exact freshVar_not_mem proofSupport 9
  have fresh_z_ne_n : z ≠ n := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_z : n ≠ z := Ne.symm fresh_z_ne_n
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 10 ∉ proofSupport
    exact freshVar_not_mem proofSupport 10
  have fresh_f_ne_n : f ≠ n := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_f : n ≠ f := Ne.symm fresh_f_ne_n
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 11 ∉ proofSupport
    exact freshVar_not_mem proofSupport 11
  have fresh_w_ne_n : w ≠ n := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_w : n ≠ w := Ne.symm fresh_w_ne_n
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_a : m ≠ a := Ne.symm fresh_a_ne_m
  have fresh_a_ne_k : a ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_a : k ≠ a := Ne.symm fresh_a_ne_k
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_e : a ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_e_ne_a : e ≠ a := Ne.symm fresh_a_ne_e
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_ne_f : a ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 0) (j := 10) (by decide)
  have fresh_f_ne_a : f ≠ a := Ne.symm fresh_a_ne_f
  have fresh_a_ne_w : a ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 0) (j := 11) (by decide)
  have fresh_w_ne_a : w ≠ a := Ne.symm fresh_a_ne_w
  have fresh_b_ne_m : b ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_b : m ≠ b := Ne.symm fresh_b_ne_m
  have fresh_b_ne_k : b ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_b : k ≠ b := Ne.symm fresh_b_ne_k
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_ne_e : b ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_e_ne_b : e ≠ b := Ne.symm fresh_b_ne_e
  have fresh_b_ne_z : b ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
  have fresh_z_ne_b : z ≠ b := Ne.symm fresh_b_ne_z
  have fresh_b_ne_f : b ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 1) (j := 10) (by decide)
  have fresh_f_ne_b : f ≠ b := Ne.symm fresh_b_ne_f
  have fresh_b_ne_w : b ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 1) (j := 11) (by decide)
  have fresh_w_ne_b : w ≠ b := Ne.symm fresh_b_ne_w
  have fresh_m_ne_k : m ≠ k :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have fresh_m_ne_c : m ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_m_ne_d : m ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_m_ne_y : m ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_m_ne_e : m ≠ e :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_e_ne_m : e ≠ m := Ne.symm fresh_m_ne_e
  have fresh_m_ne_z : m ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
  have fresh_z_ne_m : z ≠ m := Ne.symm fresh_m_ne_z
  have fresh_m_ne_f : m ≠ f :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 2) (j := 10) (by decide)
  have fresh_f_ne_m : f ≠ m := Ne.symm fresh_m_ne_f
  have fresh_m_ne_w : m ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 2) (j := 11) (by decide)
  have fresh_w_ne_m : w ≠ m := Ne.symm fresh_m_ne_w
  have fresh_k_ne_c : k ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_c_ne_k : c ≠ k := Ne.symm fresh_k_ne_c
  have fresh_k_ne_x : k ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_x_ne_k : x ≠ k := Ne.symm fresh_k_ne_x
  have fresh_k_ne_d : k ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_k : d ≠ k := Ne.symm fresh_k_ne_d
  have fresh_k_ne_y : k ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_y_ne_k : y ≠ k := Ne.symm fresh_k_ne_y
  have fresh_k_ne_e : k ≠ e :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_e_ne_k : e ≠ k := Ne.symm fresh_k_ne_e
  have fresh_k_ne_z : k ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_z_ne_k : z ≠ k := Ne.symm fresh_k_ne_z
  have fresh_k_ne_f : k ≠ f :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 3) (j := 10) (by decide)
  have fresh_f_ne_k : f ≠ k := Ne.symm fresh_k_ne_f
  have fresh_k_ne_w : k ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 3) (j := 11) (by decide)
  have fresh_w_ne_k : w ≠ k := Ne.symm fresh_k_ne_w
  have fresh_c_ne_x : c ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_c_ne_y : c ≠ y :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_y_ne_c : y ≠ c := Ne.symm fresh_c_ne_y
  have fresh_c_ne_e : c ≠ e :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_e_ne_c : e ≠ c := Ne.symm fresh_c_ne_e
  have fresh_c_ne_z : c ≠ z :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 4) (j := 9) (by decide)
  have fresh_z_ne_c : z ≠ c := Ne.symm fresh_c_ne_z
  have fresh_c_ne_f : c ≠ f :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 4) (j := 10) (by decide)
  have fresh_f_ne_c : f ≠ c := Ne.symm fresh_c_ne_f
  have fresh_c_ne_w : c ≠ w :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 4) (j := 11) (by decide)
  have fresh_w_ne_c : w ≠ c := Ne.symm fresh_c_ne_w
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_e : x ≠ e :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_e_ne_x : e ≠ x := Ne.symm fresh_x_ne_e
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_f : x ≠ f :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 5) (j := 10) (by decide)
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 5) (j := 11) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_d_ne_y : d ≠ y :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_y_ne_d : y ≠ d := Ne.symm fresh_d_ne_y
  have fresh_d_ne_e : d ≠ e :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
  have fresh_d_ne_z : d ≠ z :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_z_ne_d : z ≠ d := Ne.symm fresh_d_ne_z
  have fresh_d_ne_f : d ≠ f :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 6) (j := 10) (by decide)
  have fresh_f_ne_d : f ≠ d := Ne.symm fresh_d_ne_f
  have fresh_d_ne_w : d ≠ w :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 6) (j := 11) (by decide)
  have fresh_w_ne_d : w ≠ d := Ne.symm fresh_d_ne_w
  have fresh_y_ne_e : y ≠ e :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_e_ne_y : e ≠ y := Ne.symm fresh_y_ne_e
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 7) (j := 9) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_f : y ≠ f :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 7) (j := 10) (by decide)
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 7) (j := 11) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_e_ne_z : e ≠ z :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_e_ne_f : e ≠ f :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 8) (j := 10) (by decide)
  have fresh_f_ne_e : f ≠ e := Ne.symm fresh_e_ne_f
  have fresh_e_ne_w : e ≠ w :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 8) (j := 11) (by decide)
  have fresh_w_ne_e : w ≠ e := Ne.symm fresh_e_ne_w
  have fresh_z_ne_f : z ≠ f :=
    by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
  have fresh_f_ne_z : f ≠ z := Ne.symm fresh_z_ne_f
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 9) (j := 11) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_f_ne_w : f ≠ w :=
    by
    change freshVar proofSupport 10 ≠ freshVar proofSupport 11
    exact freshVar_injective proofSupport (i := 10) (j := 11) (by decide)
  let syntaxFormula0000 : Wff :=
    (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv m)) (.classMem (syn_cpw1 (.cv b)) (.cv m)))
  let syntaxFormula0001 : Wff :=
    (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classMem (syn_cpw1 (.cv b)) (syn_c0c)))
  let syntaxFormula0002 : Wff :=
    (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv k)) (.classMem (syn_cpw1 (.cv b)) (.cv k)))
  let syntaxFormula0003 : Wff :=
    (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (syn_cpw1 (.cv b)) (syn_cplc (.cv k) (syn_c1c))))
  let syntaxFormula0004 : Wff :=
    (syn_wrex x (syn_ccompl (.cv c))
      (.classEq (syn_cpw1 (.cv a)) (syn_cun (.cv c) (syn_csn (.cv x)))))
  let syntaxFormula0005 : Wff :=
    (syn_wrex y (syn_ccompl (.cv d))
      (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv d) (syn_csn (.cv y)))))
  let syntaxFormula0006 : Wff :=
    (syn_wa (.classEq (syn_cpw1 (.cv a)) (syn_cun (.cv c) (syn_csn (.cv x))))
      (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv d) (syn_csn (.cv y)))))
  let syntaxFormula0007 : Wff := (syn_wrex y (syn_ccompl (.cv d)) syntaxFormula0006)
  let syntaxFormula0008 : Wff := (syn_wrex x (syn_ccompl (.cv c)) syntaxFormula0007)
  let syntaxFormula0009 : Wff := (syn_wa syntaxFormula0004 syntaxFormula0005)
  let syntaxFormula0010 : Wff := (syn_wrex d (.cv k) syntaxFormula0008)
  let syntaxFormula0011 : Wff := (syn_wrex c (.cv k) syntaxFormula0010)
  let syntaxFormula0012 : Wff :=
    (syn_wa (.classMem (syn_cpw1 (.cv e)) (.cv k)) (.classMem (syn_cpw1 (.cv f)) (.cv k)))
  let syntaxFormula0013 : Wff :=
    (syn_wa (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (.cv m))
      (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (.cv m)))
  let syntaxFormula0014 : Wff := (syn_wrex m (syn_cnnc) syntaxFormula0013)
  let syntaxFormula0015 : Wff :=
    (syn_w3a (.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))
      (.classEq (.cv c) (syn_cpw1 (.cv e))) (.classEq (.cv x) (syn_csn (.cv z))))
  let syntaxFormula0016 : Wff :=
    (syn_w3a (.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))
      (.classEq (.cv d) (syn_cpw1 (.cv f))) (.classEq (.cv y) (syn_csn (.cv w))))
  let syntaxFormula0017 : Wff := (syn_wa syntaxFormula0015 syntaxFormula0016)
  let syntaxFormula0018 : Wff :=
    (syn_wa (.classMem (.cv x) (syn_ccompl (.cv c))) (.classMem (.cv y) (syn_ccompl (.cv d))))
  let syntaxFormula0019 : Wff := (syn_wex w syntaxFormula0017)
  let syntaxFormula0020 : Wff := (syn_wex z syntaxFormula0019)
  let syntaxFormula0021 : Wff := (syn_wex z syntaxFormula0015)
  let syntaxFormula0022 : Wff := (syn_wex w syntaxFormula0016)
  let syntaxFormula0023 : Wff := (syn_wa syntaxFormula0021 syntaxFormula0022)
  let syntaxFormula0024 : Wff := (syn_wex f syntaxFormula0020)
  let syntaxFormula0025 : Wff := (syn_wex e syntaxFormula0024)
  let syntaxFormula0026 : Wff :=
    (.imp (syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))))
  have p0000 :=
    @g_ncfinlowerlem1 m n a b (show a ≠ b from (by exact fresh_a_ne_b))
      (show a ≠ m from (by exact fresh_a_ne_m)) (show a ≠ n from (by exact fresh_a_ne_n))
      (show b ≠ m from (by exact fresh_b_ne_m)) (show b ≠ n from (by exact fresh_b_ne_n))
      (show m ≠ n from (by exact fresh_m_ne_n))
  have p0001 := @g_eleq2 (.cv m) (syn_c0c) (syn_cpw1 (.cv a))
  have p0002 := @g_eleq2 (.cv m) (syn_c0c) (syn_cpw1 (.cv b))
  have p0003 :=
    @g_anbi12d (.classEq (.cv m) (syn_c0c)) (.classMem (syn_cpw1 (.cv a)) (.cv m))
      (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classMem (syn_cpw1 (.cv b)) (.cv m))
      (.classMem (syn_cpw1 (.cv b)) (syn_c0c)) p0001 p0002
  have p0004 :=
    @g_imbi1d (.classEq (.cv m) (syn_c0c)) syntaxFormula0000 syntaxFormula0001
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))) p0003
  have freshnessCertificate0000 : a ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ m from (by exact fresh_a_ne_m)))))
  have freshnessCertificate0001 : a ∉ ((syn_c0c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0002 : a ∉ (((Class.cv m)).fv) ∪ (((syn_c0c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0000 freshnessCertificate0001))
  have freshnessCertificate0003 : a ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0002)
  have freshnessCertificate0004 : b ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ m from (by exact fresh_b_ne_m)))))
  have freshnessCertificate0005 : b ∉ ((syn_c0c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0006 : b ∉ (((Class.cv m)).fv) ∪ (((syn_c0c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0004 freshnessCertificate0005))
  have freshnessCertificate0007 : b ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0006)
  have p0005 :=
    @g_n_2albidv (.classEq (.cv m) (syn_c0c))
      (.imp syntaxFormula0000 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      (.imp syntaxFormula0001 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      a b (by exact freshnessCertificate0003) (by exact freshnessCertificate0007) p0004
  have p0006 := @g_eleq2 (.cv m) (.cv k) (syn_cpw1 (.cv a))
  have p0007 := @g_eleq2 (.cv m) (.cv k) (syn_cpw1 (.cv b))
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (syn_wb (.classMem (syn_cpw1 (.cv a)) (.cv m))
          (.classMem (syn_cpw1 (.cv a)) (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa,
          syn_cpw, syn_wss, syn_c1c, syn_wex, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0008_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (syn_wb (.classMem (syn_cpw1 (.cv b)) (.cv m))
          (.classMem (syn_cpw1 (.cv b)) (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa,
          syn_cpw, syn_wss, syn_c1c, syn_wex, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_anbi12d (.objEq m k) (.classMem (syn_cpw1 (.cv a)) (.cv m))
      (.classMem (syn_cpw1 (.cv a)) (.cv k)) (.classMem (syn_cpw1 (.cv b)) (.cv m))
      (.classMem (syn_cpw1 (.cv b)) (.cv k)) p0008_e00_recanon p0008_e01_recanon
  have p0009 :=
    @g_imbi1d (.objEq m k) syntaxFormula0000 syntaxFormula0002
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))) p0008
  have freshnessCertificate0008 : a ∉ ({ m, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show a ≠ m from (by exact fresh_a_ne_m)),
          (show a ≠ k from (by exact fresh_a_ne_k))⟩)
  have freshnessCertificate0009 : a ∉ ((Wff.objEq m k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact freshnessCertificate0008)
  have freshnessCertificate0010 : b ∉ ({ m, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show b ≠ m from (by exact fresh_b_ne_m)),
          (show b ≠ k from (by exact fresh_b_ne_k))⟩)
  have freshnessCertificate0011 : b ∉ ((Wff.objEq m k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact freshnessCertificate0010)
  have p0010 :=
    @g_n_2albidv (.objEq m k)
      (.imp syntaxFormula0000 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      (.imp syntaxFormula0002 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      a b (by exact freshnessCertificate0009) (by exact freshnessCertificate0011) p0009
  have p0011 := @g_eleq2 (.cv m) (syn_cplc (.cv k) (syn_c1c)) (syn_cpw1 (.cv a))
  have p0012 := @g_eleq2 (.cv m) (syn_cplc (.cv k) (syn_c1c)) (syn_cpw1 (.cv b))
  have p0013 :=
    @g_anbi12d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (syn_cpw1 (.cv a)) (.cv m))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (syn_cpw1 (.cv b)) (.cv m))
      (.classMem (syn_cpw1 (.cv b)) (syn_cplc (.cv k) (syn_c1c))) p0011 p0012
  have p0014 :=
    @g_imbi1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) syntaxFormula0000
      syntaxFormula0003 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))) p0013
  have freshnessCertificate0012 : a ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ k from (by exact fresh_a_ne_k)))))
  have freshnessCertificate0013 : a ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0014 : a ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0012 freshnessCertificate0013))
  have freshnessCertificate0015 : a ∉ ((syn_cplc (.cv k) (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0014)
  have freshnessCertificate0016 :
    a ∉ (((Class.cv m)).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0000 freshnessCertificate0015))
  have freshnessCertificate0017 :
    a ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0016)
  have freshnessCertificate0018 : b ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ k from (by exact fresh_b_ne_k)))))
  have freshnessCertificate0019 : b ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0020 : b ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0018 freshnessCertificate0019))
  have freshnessCertificate0021 : b ∉ ((syn_cplc (.cv k) (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0020)
  have freshnessCertificate0022 :
    b ∉ (((Class.cv m)).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0004 freshnessCertificate0021))
  have freshnessCertificate0023 :
    b ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0022)
  have p0015 :=
    @g_n_2albidv (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (.imp syntaxFormula0000 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      (.imp syntaxFormula0003 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      a b (by exact freshnessCertificate0017) (by exact freshnessCertificate0023) p0014
  have p0016 := @g_eleq2 (.cv m) M (syn_cpw1 (.cv a))
  have p0017 := @g_eleq2 (.cv m) M (syn_cpw1 (.cv b))
  have p0018 :=
    @g_anbi12d (.classEq (.cv m) M) (.classMem (syn_cpw1 (.cv a)) (.cv m))
      (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) (.cv m))
      (.classMem (syn_cpw1 (.cv b)) M) p0016 p0017
  have p0019 :=
    @g_imbi1d (.classEq (.cv m) M) syntaxFormula0000
      (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))) p0018
  have freshnessCertificate0024 : a ∉ (((Class.cv m)).fv) ∪ ((M).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0000
        (show a ∉ (M).fv from (by exact fresh_a_not_M)))
  have freshnessCertificate0025 : a ∉ ((Wff.classEq (.cv m) M)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0024)
  have freshnessCertificate0026 : b ∉ (((Class.cv m)).fv) ∪ ((M).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0004
        (show b ∉ (M).fv from (by exact fresh_b_not_M)))
  have freshnessCertificate0027 : b ∉ ((Wff.classEq (.cv m) M)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0026)
  have p0020 :=
    @g_n_2albidv (.classEq (.cv m) M)
      (.imp syntaxFormula0000 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      (.imp (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
        (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      a b (by exact freshnessCertificate0025) (by exact freshnessCertificate0027) p0019
  have p0021 := @g_el0c (syn_cpw1 (.cv a))
  have p0022 := @g_pw10b (.cv a)
  have p0023 :=
    @g_bitri (.classMem (syn_cpw1 (.cv a)) (syn_c0c))
      (.classEq (syn_cpw1 (.cv a)) (syn_c0)) (.classEq (.cv a) (syn_c0)) p0021 p0022
  have p0024 := @g_el0c (syn_cpw1 (.cv b))
  have p0025 := @g_pw10b (.cv b)
  have p0026 :=
    @g_bitri (.classMem (syn_cpw1 (.cv b)) (syn_c0c))
      (.classEq (syn_cpw1 (.cv b)) (syn_c0)) (.classEq (.cv b) (syn_c0)) p0024 p0025
  have p0027 := @g_peano1
  have p0028 := @g_nulel0c
  have p0029 := @g_eleq2 (.cv n) (syn_c0c) (syn_c0)
  have freshnessCertificate0028 : n ∉ ((syn_c0c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0029 : n ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0030 : n ∉ ((syn_c0)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0031 : n ∉ (((syn_c0)).fv) ∪ (((syn_c0c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0030 freshnessCertificate0028))
  have freshnessCertificate0032 : n ∉ ((Wff.classMem (syn_c0) (syn_c0c))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0031)
  have p0030 :=
    @g_rspcev (.classMem (syn_c0) (.cv n)) (.classMem (syn_c0) (syn_c0c)) n (syn_c0c)
      (syn_cnnc) (by exact freshnessCertificate0028) (by exact freshnessCertificate0029)
      (by exact freshnessCertificate0032) p0029
  have p0031 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0) (syn_c0c))
      (syn_wrex n (syn_cnnc) (.classMem (syn_c0) (.cv n))) p0027 p0028 p0030
  have p0032 := @g_eleq1 (.cv a) (syn_c0) (.cv n)
  have p0033 := @g_eleq1 (.cv b) (syn_c0) (.cv n)
  have p0034_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (syn_c0)) (syn_wb (.objMem a n) (.classMem (syn_c0) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_c0, syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa,
          syn_cvv, syn_wb]
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
      p0032
  have p0034_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (syn_c0)) (syn_wb (.objMem b n) (.classMem (syn_c0) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_c0, syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa,
          syn_cvv, syn_wb]
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
      p0033
  have p0034 :=
    @g_bi2anan9 (.classEq (.cv a) (syn_c0)) (.objMem a n) (.classMem (syn_c0) (.cv n))
      (.classEq (.cv b) (syn_c0)) (.objMem b n) (.classMem (syn_c0) (.cv n))
      p0034_e00_recanon p0034_e01_recanon
  have p0035 := @g_anidm (.classMem (syn_c0) (.cv n))
  have p0036 :=
    @g_syl6bb (syn_wa (.classEq (.cv a) (syn_c0)) (.classEq (.cv b) (syn_c0)))
      (syn_wa (.objMem a n) (.objMem b n))
      (syn_wa (.classMem (syn_c0) (.cv n)) (.classMem (syn_c0) (.cv n)))
      (.classMem (syn_c0) (.cv n)) p0034 p0035
  have freshnessCertificate0033 : n ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ a from (by exact fresh_n_ne_a)))))
  have freshnessCertificate0034 : n ∉ (((Class.cv a)).fv) ∪ (((syn_c0)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0033 freshnessCertificate0030))
  have freshnessCertificate0035 : n ∉ ((Wff.classEq (.cv a) (syn_c0))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0034)
  have freshnessCertificate0036 : n ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ b from (by exact fresh_n_ne_b)))))
  have freshnessCertificate0037 : n ∉ (((Class.cv b)).fv) ∪ (((syn_c0)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0036 freshnessCertificate0030))
  have freshnessCertificate0038 : n ∉ ((Wff.classEq (.cv b) (syn_c0))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0037)
  have freshnessCertificate0039 :
    n ∉ (((Wff.classEq (.cv a) (syn_c0))).fv) ∪ (((Wff.classEq (.cv b) (syn_c0))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0035 freshnessCertificate0038))
  have freshnessCertificate0040 :
    n ∉ ((syn_wa (.classEq (.cv a) (syn_c0)) (.classEq (.cv b) (syn_c0)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0039)
  have p0037 :=
    @g_rexbidv (syn_wa (.classEq (.cv a) (syn_c0)) (.classEq (.cv b) (syn_c0)))
      (syn_wa (.objMem a n) (.objMem b n)) (.classMem (syn_c0) (.cv n)) n (syn_cnnc)
      (by exact freshnessCertificate0040) p0036
  have p0038 :=
    @g_mpbiri (syn_wa (.classEq (.cv a) (syn_c0)) (.classEq (.cv b) (syn_c0)))
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))
      (syn_wrex n (syn_cnnc) (.classMem (syn_c0) (.cv n))) p0031 p0037
  have p0039 :=
    @g_syl2anb (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classEq (.cv a) (syn_c0))
      (.classEq (.cv b) (syn_c0))
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))
      (.classMem (syn_cpw1 (.cv b)) (syn_c0c)) p0023 p0026 p0038
  have p0040 :=
    @g_gen2
      (.imp syntaxFormula0001 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      a b p0039
  have freshnessCertificate0041 : a ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0042 : a ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0012 freshnessCertificate0041))
  have freshnessCertificate0043 : a ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0042)
  have p0041 :=
    @g_nfv (.classMem (.cv k) (syn_cnnc)) a (by exact freshnessCertificate0043)
  have p0042 :=
    @g_nfa1
      (.all b (.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))
      a
  have p0043 :=
    @g_nfan (.classMem (.cv k) (syn_cnnc))
      (.all a (.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      a p0041 p0042
  have freshnessCertificate0044 : b ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0045 : b ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0018 freshnessCertificate0044))
  have freshnessCertificate0046 : b ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0045)
  have p0044 :=
    @g_nfv (.classMem (.cv k) (syn_cnnc)) b (by exact freshnessCertificate0046)
  have p0045 :=
    @g_nfa2
      (.imp syntaxFormula0002 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      b a
  have p0046 :=
    @g_nfan (.classMem (.cv k) (syn_cnnc))
      (.all a (.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      b p0044 p0045
  have freshnessCertificate0047 : d ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ k from (by exact fresh_d_ne_k)))))
  have freshnessCertificate0048 : c ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ k from (by exact fresh_c_ne_k)))))
  have freshnessCertificate0049 : d ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ c from (by exact fresh_d_ne_c)))))
  have freshnessCertificate0050 : d ∉ ((syn_ccompl (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0049)
  have freshnessCertificate0051 : d ∉ (((syn_ccompl (.cv c))).fv).erase x :=
    (fun hmem => freshnessCertificate0050 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0052 : d ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ a from (by exact fresh_d_ne_a)))))
  have freshnessCertificate0053 : d ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0052)
  have freshnessCertificate0054 : d ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ x from (by exact fresh_d_ne_x)))))
  have freshnessCertificate0055 : d ∉ ((syn_csn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0054)
  have freshnessCertificate0056 : d ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0049 freshnessCertificate0055))
  have freshnessCertificate0057 : d ∉ ((syn_cun (.cv c) (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0056)
  have freshnessCertificate0058 :
    d ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_cun (.cv c) (syn_csn (.cv x)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0053 freshnessCertificate0057))
  have freshnessCertificate0059 :
    d ∉ ((Wff.classEq (syn_cpw1 (.cv a)) (syn_cun (.cv c) (syn_csn (.cv x))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0058)
  have freshnessCertificate0060 :
    d ∉
      (((Wff.classEq (syn_cpw1 (.cv a)) (syn_cun (.cv c) (syn_csn (.cv x))))).fv).erase
        x :=
    (fun hmem => freshnessCertificate0059 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0061 :
    d ∉
      ((((syn_ccompl (.cv c))).fv).erase x) ∪
        ((((Wff.classEq (syn_cpw1 (.cv a)) (syn_cun (.cv c) (syn_csn (.cv x))))).fv).erase x) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0051 freshnessCertificate0060))
  have freshnessCertificate0062 : d ∉ (syntaxFormula0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0061)
  have freshnessCertificate0063 : c ∉ ((Class.cv d)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ d } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ d from (by exact fresh_c_ne_d)))))
  have freshnessCertificate0064 : c ∉ ((syn_ccompl (.cv d))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0063)
  have freshnessCertificate0065 : c ∉ (((syn_ccompl (.cv d))).fv).erase y :=
    (fun hmem => freshnessCertificate0064 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0066 : c ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ b from (by exact fresh_c_ne_b)))))
  have freshnessCertificate0067 : c ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0066)
  have freshnessCertificate0068 : c ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ y from (by exact fresh_c_ne_y)))))
  have freshnessCertificate0069 : c ∉ ((syn_csn (.cv y))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0068)
  have freshnessCertificate0070 : c ∉ (((Class.cv d)).fv) ∪ (((syn_csn (.cv y))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0063 freshnessCertificate0069))
  have freshnessCertificate0071 : c ∉ ((syn_cun (.cv d) (syn_csn (.cv y)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0070)
  have freshnessCertificate0072 :
    c ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((syn_cun (.cv d) (syn_csn (.cv y)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0067 freshnessCertificate0071))
  have freshnessCertificate0073 :
    c ∉ ((Wff.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv d) (syn_csn (.cv y))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0072)
  have freshnessCertificate0074 :
    c ∉
      (((Wff.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv d) (syn_csn (.cv y))))).fv).erase
        y :=
    (fun hmem => freshnessCertificate0073 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0075 :
    c ∉
      ((((syn_ccompl (.cv d))).fv).erase y) ∪
        ((((Wff.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv d) (syn_csn (.cv y))))).fv).erase y) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0065 freshnessCertificate0074))
  have freshnessCertificate0076 : c ∉ (syntaxFormula0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0075)
  have p0047 :=
    @g_reeanv syntaxFormula0004 syntaxFormula0005 c d (.cv k) (.cv k)
      (by exact freshnessCertificate0047) (by exact freshnessCertificate0048)
      (by exact freshnessCertificate0062) (by exact freshnessCertificate0076)
      (show c ≠ d from (by exact fresh_c_ne_d))
  have freshnessCertificate0077 : y ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ c from (by exact fresh_y_ne_c)))))
  have freshnessCertificate0078 : y ∉ ((syn_ccompl (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0077)
  have freshnessCertificate0079 : x ∉ ((Class.cv d)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ d } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ d from (by exact fresh_x_ne_d)))))
  have freshnessCertificate0080 : x ∉ ((syn_ccompl (.cv d))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0079)
  have freshnessCertificate0081 : y ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ a from (by exact fresh_y_ne_a)))))
  have freshnessCertificate0082 : y ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0081)
  have freshnessCertificate0083 : y ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ x from (by exact fresh_y_ne_x)))))
  have freshnessCertificate0084 : y ∉ ((syn_csn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0083)
  have freshnessCertificate0085 : y ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0077 freshnessCertificate0084))
  have freshnessCertificate0086 : y ∉ ((syn_cun (.cv c) (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0085)
  have freshnessCertificate0087 :
    y ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_cun (.cv c) (syn_csn (.cv x)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0082 freshnessCertificate0086))
  have freshnessCertificate0088 :
    y ∉ ((Wff.classEq (syn_cpw1 (.cv a)) (syn_cun (.cv c) (syn_csn (.cv x))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0087)
  have freshnessCertificate0089 : x ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ b from (by exact fresh_x_ne_b)))))
  have freshnessCertificate0090 : x ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0089)
  have freshnessCertificate0091 : x ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ y from (by exact fresh_x_ne_y)))))
  have freshnessCertificate0092 : x ∉ ((syn_csn (.cv y))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0091)
  have freshnessCertificate0093 : x ∉ (((Class.cv d)).fv) ∪ (((syn_csn (.cv y))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0079 freshnessCertificate0092))
  have freshnessCertificate0094 : x ∉ ((syn_cun (.cv d) (syn_csn (.cv y)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0093)
  have freshnessCertificate0095 :
    x ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((syn_cun (.cv d) (syn_csn (.cv y)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0090 freshnessCertificate0094))
  have freshnessCertificate0096 :
    x ∉ ((Wff.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv d) (syn_csn (.cv y))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0095)
  have p0048 :=
    @g_reeanv (.classEq (syn_cpw1 (.cv a)) (syn_cun (.cv c) (syn_csn (.cv x))))
      (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv d) (syn_csn (.cv y)))) x y
      (syn_ccompl (.cv c)) (syn_ccompl (.cv d)) (by exact freshnessCertificate0078)
      (by exact freshnessCertificate0080) (by exact freshnessCertificate0088)
      (by exact freshnessCertificate0096) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0049 := @g_n_2rexbii syntaxFormula0008 syntaxFormula0009 c d (.cv k) (.cv k) p0048
  have freshnessCertificate0097 : c ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ a from (by exact fresh_c_ne_a)))))
  have freshnessCertificate0098 : c ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0097)
  have freshnessCertificate0099 : x ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ a from (by exact fresh_x_ne_a)))))
  have freshnessCertificate0100 : x ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0099)
  have p0050 :=
    @g_elsuc x (syn_cpw1 (.cv a)) (.cv k) c (by exact freshnessCertificate0098)
      (by exact freshnessCertificate0100) (by exact freshnessCertificate0048)
      (show c ≠ x from (by exact fresh_c_ne_x))
  have freshnessCertificate0101 : d ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ b from (by exact fresh_d_ne_b)))))
  have freshnessCertificate0102 : d ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0101)
  have freshnessCertificate0103 : y ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ b from (by exact fresh_y_ne_b)))))
  have freshnessCertificate0104 : y ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0103)
  have p0051 :=
    @g_elsuc y (syn_cpw1 (.cv b)) (.cv k) d (by exact freshnessCertificate0102)
      (by exact freshnessCertificate0104) (by exact freshnessCertificate0047)
      (show d ≠ y from (by exact fresh_d_ne_y))
  have p0052 :=
    @g_anbi12i (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wrex c (.cv k) syntaxFormula0004)
      (.classMem (syn_cpw1 (.cv b)) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wrex d (.cv k) syntaxFormula0005) p0050 p0051
  have p0053 :=
    @g_n_3bitr4ri (syn_wrex c (.cv k) (syn_wrex d (.cv k) syntaxFormula0009))
      (syn_wa (syn_wrex c (.cv k) syntaxFormula0004) (syn_wrex d (.cv k) syntaxFormula0005))
      syntaxFormula0011 syntaxFormula0003 p0047 p0049 p0052
  have p0054 := @g_vex e
  have p0055 := @g_vex f
  have p0056 := @g_pw1eq (.cv a) (.cv e)
  have p0057_e00_recanon :
    Nominal.NPrf (.imp (.objEq a e) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv e)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa, syn_cpw,
          syn_wss, syn_c1c, syn_wex, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0056
  have p0057 :=
    @g_eleq1d (.objEq a e) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv e)) (.cv k) p0057_e00_recanon
  have p0058 := @g_pw1eq (.cv b) (.cv f)
  have p0059_e00_recanon :
    Nominal.NPrf (.imp (.objEq b f) (.classEq (syn_cpw1 (.cv b)) (syn_cpw1 (.cv f)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa, syn_cpw,
          syn_wss, syn_c1c, syn_wex, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @g_eleq1d (.objEq b f) (syn_cpw1 (.cv b)) (syn_cpw1 (.cv f)) (.cv k) p0059_e00_recanon
  have p0060 :=
    @g_bi2anan9 (.objEq a e) (.classMem (syn_cpw1 (.cv a)) (.cv k))
      (.classMem (syn_cpw1 (.cv e)) (.cv k)) (.objEq b f)
      (.classMem (syn_cpw1 (.cv b)) (.cv k)) (.classMem (syn_cpw1 (.cv f)) (.cv k)) p0057
      p0059
  have p0061 := @g_elequ1 a e n
  have p0062 := @g_elequ1 b f n
  have p0063 :=
    @g_bi2anan9 (.objEq a e) (.objMem a n) (.objMem e n) (.objEq b f) (.objMem b n)
      (.objMem f n) p0061 p0062
  have freshnessCertificate0105 : n ∉ ({ a, e } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show n ≠ a from (by exact fresh_n_ne_a)),
          (show n ≠ e from (by exact fresh_n_ne_e))⟩)
  have freshnessCertificate0106 : n ∉ ((Wff.objEq a e)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact freshnessCertificate0105)
  have freshnessCertificate0107 : n ∉ ({ b, f } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show n ≠ b from (by exact fresh_n_ne_b)),
          (show n ≠ f from (by exact fresh_n_ne_f))⟩)
  have freshnessCertificate0108 : n ∉ ((Wff.objEq b f)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact freshnessCertificate0107)
  have freshnessCertificate0109 : n ∉ (((Wff.objEq a e)).fv) ∪ (((Wff.objEq b f)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0106 freshnessCertificate0108))
  have freshnessCertificate0110 : n ∉ ((syn_wa (.objEq a e) (.objEq b f))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0109)
  have p0064 :=
    @g_rexbidv (syn_wa (.objEq a e) (.objEq b f)) (syn_wa (.objMem a n) (.objMem b n))
      (syn_wa (.objMem e n) (.objMem f n)) n (syn_cnnc)
      (by exact freshnessCertificate0110) p0063
  have p0065 :=
    @g_imbi12d (syn_wa (.objEq a e) (.objEq b f)) syntaxFormula0002 syntaxFormula0012
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n))) p0060 p0064
  have p0066_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv a) (.cv e)) (.classEq (.cv b) (.cv f))) (syn_wb
          (.imp syntaxFormula0002 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
          (.imp syntaxFormula0012
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_wb, syn_wrex, syn_wex, syn_cnnc, syn_cint]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0065
  have freshnessCertificate0111 : a ∉ ((Class.cv e)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ e } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ e from (by exact fresh_a_ne_e)))))
  have freshnessCertificate0112 : b ∉ ((Class.cv e)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ e } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ e from (by exact fresh_b_ne_e)))))
  have freshnessCertificate0113 : a ∉ ((Class.cv f)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ f } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ f from (by exact fresh_a_ne_f)))))
  have freshnessCertificate0114 : b ∉ ((Class.cv f)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ f } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ f from (by exact fresh_b_ne_f)))))
  have freshnessCertificate0115 : a ∉ ((syn_cpw1 (.cv e))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0111)
  have freshnessCertificate0116 : a ∉ (((syn_cpw1 (.cv e))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0115 freshnessCertificate0012))
  have freshnessCertificate0117 : a ∉ ((Wff.classMem (syn_cpw1 (.cv e)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0116)
  have freshnessCertificate0118 : a ∉ ((syn_cpw1 (.cv f))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0113)
  have freshnessCertificate0119 : a ∉ (((syn_cpw1 (.cv f))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0118 freshnessCertificate0012))
  have freshnessCertificate0120 : a ∉ ((Wff.classMem (syn_cpw1 (.cv f)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0119)
  have freshnessCertificate0121 :
    a ∉
      (((Wff.classMem (syn_cpw1 (.cv e)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv f)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0117 freshnessCertificate0120))
  have freshnessCertificate0122 : a ∉ (syntaxFormula0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0121)
  have freshnessCertificate0123 : a ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0041 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0124 : a ∉ ({ e, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show a ≠ e from (by exact fresh_a_ne_e)),
          (show a ≠ n from (by exact fresh_a_ne_n))⟩)
  have freshnessCertificate0125 : a ∉ ((Wff.objMem e n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0124)
  have freshnessCertificate0126 : a ∉ ({ f, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show a ≠ f from (by exact fresh_a_ne_f)),
          (show a ≠ n from (by exact fresh_a_ne_n))⟩)
  have freshnessCertificate0127 : a ∉ ((Wff.objMem f n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0126)
  have freshnessCertificate0128 : a ∉ (((Wff.objMem e n)).fv) ∪ (((Wff.objMem f n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0125 freshnessCertificate0127))
  have freshnessCertificate0129 : a ∉ ((syn_wa (.objMem e n) (.objMem f n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0128)
  have freshnessCertificate0130 :
    a ∉ (((syn_wa (.objMem e n) (.objMem f n))).fv).erase n :=
    (fun hmem => freshnessCertificate0129 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0131 :
    a ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem e n) (.objMem f n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0123 freshnessCertificate0130))
  have freshnessCertificate0132 :
    a ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0131)
  have freshnessCertificate0133 :
    a ∉
      ((syntaxFormula0012).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0122 freshnessCertificate0132))
  have freshnessCertificate0134 :
    a ∉
      ((Wff.imp syntaxFormula0012
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0133)
  have freshnessCertificate0135 : b ∉ ((syn_cpw1 (.cv e))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0112)
  have freshnessCertificate0136 : b ∉ (((syn_cpw1 (.cv e))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0135 freshnessCertificate0018))
  have freshnessCertificate0137 : b ∉ ((Wff.classMem (syn_cpw1 (.cv e)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0136)
  have freshnessCertificate0138 : b ∉ ((syn_cpw1 (.cv f))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0114)
  have freshnessCertificate0139 : b ∉ (((syn_cpw1 (.cv f))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0138 freshnessCertificate0018))
  have freshnessCertificate0140 : b ∉ ((Wff.classMem (syn_cpw1 (.cv f)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0139)
  have freshnessCertificate0141 :
    b ∉
      (((Wff.classMem (syn_cpw1 (.cv e)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv f)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0137 freshnessCertificate0140))
  have freshnessCertificate0142 : b ∉ (syntaxFormula0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0141)
  have freshnessCertificate0143 : b ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0044 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0144 : b ∉ ({ e, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show b ≠ e from (by exact fresh_b_ne_e)),
          (show b ≠ n from (by exact fresh_b_ne_n))⟩)
  have freshnessCertificate0145 : b ∉ ((Wff.objMem e n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0144)
  have freshnessCertificate0146 : b ∉ ({ f, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show b ≠ f from (by exact fresh_b_ne_f)),
          (show b ≠ n from (by exact fresh_b_ne_n))⟩)
  have freshnessCertificate0147 : b ∉ ((Wff.objMem f n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0146)
  have freshnessCertificate0148 : b ∉ (((Wff.objMem e n)).fv) ∪ (((Wff.objMem f n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0145 freshnessCertificate0147))
  have freshnessCertificate0149 : b ∉ ((syn_wa (.objMem e n) (.objMem f n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0148)
  have freshnessCertificate0150 :
    b ∉ (((syn_wa (.objMem e n) (.objMem f n))).fv).erase n :=
    (fun hmem => freshnessCertificate0149 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0151 :
    b ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem e n) (.objMem f n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0143 freshnessCertificate0150))
  have freshnessCertificate0152 :
    b ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0151)
  have freshnessCertificate0153 :
    b ∉
      ((syntaxFormula0012).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0142 freshnessCertificate0152))
  have freshnessCertificate0154 :
    b ∉
      ((Wff.imp syntaxFormula0012
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0153)
  have p0066 :=
    @g_spc2gv
      (.imp syntaxFormula0002 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      (.imp syntaxFormula0012 (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n))))
      a b (.cv e) (.cv f) (syn_cvv) (syn_cvv) (by exact freshnessCertificate0111)
      (by exact freshnessCertificate0112) (by exact freshnessCertificate0113)
      (by exact freshnessCertificate0114) (by exact freshnessCertificate0134)
      (by exact freshnessCertificate0154) (show a ≠ b from (by exact fresh_a_ne_b))
      p0066_e00_recanon
  have p0067 :=
    @g_mp2an (.classMem (.cv e) (syn_cvv)) (.classMem (.cv f) (syn_cvv))
      (.imp (.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
        (.imp syntaxFormula0012 (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n)))))
      p0054 p0055 p0066
  have p0068 :=
    @g_com12
      (.all a (.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      syntaxFormula0012 (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n))) p0067
  have p0069 :=
    @g_ad2antrl syntaxFormula0012
      (.imp (.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
        (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n))))
      (.classMem (.cv k) (syn_cnnc)) (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))
      p0068
  have p0070 := @g_peano2 (.cv n)
  have p0071 :=
    @g_ad2antrl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (syn_wa (.objMem e n) (.objMem f n)) p0070
  have p0072 :=
    @g_simprrl
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (.classMem (.cv n) (syn_cnnc)) (.objMem e n) (.objMem f n)
  have p0073 :=
    @g_simprrl (.classMem (.cv k) (syn_cnnc)) syntaxFormula0012 (.neg (.objMem z e))
      (.neg (.objMem w f))
  have p0074 :=
    @g_adantr
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (.neg (.objMem z e))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem e n) (.objMem f n))) p0073
  have p0075 := @g_vex z
  have p0076 := @g_elsuci (.cv e) (.cv n) (.cv z) p0075
  have p0077_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objMem e n) (.neg (.objMem z e)))
        (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_cun, syn_cnin, syn_wnan, syn_ccompl, syn_csn, syn_cplc,
          syn_wrex, syn_wex, syn_c1c]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0076
  have p0077 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem e n) (.objMem f n))))
      (.objMem e n) (.neg (.objMem z e))
      (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))) p0072
      p0074 p0077_e02_recanon
  have p0078 :=
    @g_simprrr
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (.classMem (.cv n) (syn_cnnc)) (.objMem e n) (.objMem f n)
  have p0079 :=
    @g_simprrr (.classMem (.cv k) (syn_cnnc)) syntaxFormula0012 (.neg (.objMem z e))
      (.neg (.objMem w f))
  have p0080 :=
    @g_adantr
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (.neg (.objMem w f))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem e n) (.objMem f n))) p0079
  have p0081 := @g_vex w
  have p0082 := @g_elsuci (.cv f) (.cv n) (.cv w) p0081
  have p0083_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objMem f n) (.neg (.objMem w f)))
        (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (syn_cplc (.cv n) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_cun, syn_cnin, syn_wnan, syn_ccompl, syn_csn, syn_cplc,
          syn_wrex, syn_wex, syn_c1c]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0082
  have p0083 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem e n) (.objMem f n))))
      (.objMem f n) (.neg (.objMem w f))
      (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (syn_cplc (.cv n) (syn_c1c))) p0078
      p0080 p0083_e02_recanon
  have p0084 :=
    @g_eleq2 (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_cun (.cv e) (syn_csn (.cv z)))
  have p0085 :=
    @g_eleq2 (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_cun (.cv f) (syn_csn (.cv w)))
  have p0086 :=
    @g_anbi12d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
      (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (.cv m))
      (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))
      (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (.cv m))
      (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (syn_cplc (.cv n) (syn_c1c))) p0084
      p0085
  have freshnessCertificate0155 : m ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ n from (by exact fresh_m_ne_n)))))
  have freshnessCertificate0156 : m ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0157 : m ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0155 freshnessCertificate0156))
  have freshnessCertificate0158 : m ∉ ((syn_cplc (.cv n) (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0157)
  have freshnessCertificate0159 : m ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0160 : m ∉ ((Class.cv e)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ e } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ e from (by exact fresh_m_ne_e)))))
  have freshnessCertificate0161 : m ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ z from (by exact fresh_m_ne_z)))))
  have freshnessCertificate0162 : m ∉ ((syn_csn (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0161)
  have freshnessCertificate0163 : m ∉ (((Class.cv e)).fv) ∪ (((syn_csn (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0160 freshnessCertificate0162))
  have freshnessCertificate0164 : m ∉ ((syn_cun (.cv e) (syn_csn (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0163)
  have freshnessCertificate0165 :
    m ∉
      (((syn_cun (.cv e) (syn_csn (.cv z)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0164 freshnessCertificate0158))
  have freshnessCertificate0166 :
    m ∉
      ((Wff.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0165)
  have freshnessCertificate0167 : m ∉ ((Class.cv f)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ f } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ f from (by exact fresh_m_ne_f)))))
  have freshnessCertificate0168 : m ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ w from (by exact fresh_m_ne_w)))))
  have freshnessCertificate0169 : m ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0168)
  have freshnessCertificate0170 : m ∉ (((Class.cv f)).fv) ∪ (((syn_csn (.cv w))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0167 freshnessCertificate0169))
  have freshnessCertificate0171 : m ∉ ((syn_cun (.cv f) (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0170)
  have freshnessCertificate0172 :
    m ∉
      (((syn_cun (.cv f) (syn_csn (.cv w)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0171 freshnessCertificate0158))
  have freshnessCertificate0173 :
    m ∉
      ((Wff.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (syn_cplc (.cv n) (syn_c1c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0172)
  have freshnessCertificate0174 :
    m ∉
      (((Wff.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv) ∪
        (((Wff.classMem (syn_cun (.cv f) (syn_csn (.cv w)))
            (syn_cplc (.cv n) (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0166 freshnessCertificate0173))
  have freshnessCertificate0175 :
    m ∉
      ((syn_wa (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))
          (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (syn_cplc (.cv n) (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0174)
  have p0087 :=
    @g_rspcev syntaxFormula0013
      (syn_wa (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))
        (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (syn_cplc (.cv n) (syn_c1c))))
      m (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc) (by exact freshnessCertificate0158)
      (by exact freshnessCertificate0159) (by exact freshnessCertificate0175) p0086
  have p0088 :=
    @g_syl12anc
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem e n) (.objMem f n))))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))
      (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (syn_cplc (.cv n) (syn_c1c)))
      syntaxFormula0014 p0071 p0077 p0083 p0087
  have p0089 :=
    @g_expr
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem e n) (.objMem f n))
      syntaxFormula0014 p0088
  have freshnessCertificate0176 : n ∉ (((syn_cnnc)).fv).erase m :=
    (fun hmem => freshnessCertificate0029 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0177 : n ∉ ((Class.cv e)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ e } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ e from (by exact fresh_n_ne_e)))))
  have freshnessCertificate0178 : n ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ z from (by exact fresh_n_ne_z)))))
  have freshnessCertificate0179 : n ∉ ((syn_csn (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0178)
  have freshnessCertificate0180 : n ∉ (((Class.cv e)).fv) ∪ (((syn_csn (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0177 freshnessCertificate0179))
  have freshnessCertificate0181 : n ∉ ((syn_cun (.cv e) (syn_csn (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0180)
  have freshnessCertificate0182 : n ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ m from (by exact fresh_n_ne_m)))))
  have freshnessCertificate0183 :
    n ∉ (((syn_cun (.cv e) (syn_csn (.cv z)))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0181 freshnessCertificate0182))
  have freshnessCertificate0184 :
    n ∉ ((Wff.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (.cv m))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0183)
  have freshnessCertificate0185 : n ∉ ((Class.cv f)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ f } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ f from (by exact fresh_n_ne_f)))))
  have freshnessCertificate0186 : n ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ w from (by exact fresh_n_ne_w)))))
  have freshnessCertificate0187 : n ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0186)
  have freshnessCertificate0188 : n ∉ (((Class.cv f)).fv) ∪ (((syn_csn (.cv w))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0185 freshnessCertificate0187))
  have freshnessCertificate0189 : n ∉ ((syn_cun (.cv f) (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0188)
  have freshnessCertificate0190 :
    n ∉ (((syn_cun (.cv f) (syn_csn (.cv w)))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0189 freshnessCertificate0182))
  have freshnessCertificate0191 :
    n ∉ ((Wff.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (.cv m))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0190)
  have freshnessCertificate0192 :
    n ∉
      (((Wff.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (.cv m))).fv) ∪
        (((Wff.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0184 freshnessCertificate0191))
  have freshnessCertificate0193 : n ∉ (syntaxFormula0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0192)
  have freshnessCertificate0194 : n ∉ ((syntaxFormula0013).fv).erase m :=
    (fun hmem => freshnessCertificate0193 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0195 :
    n ∉ ((((syn_cnnc)).fv).erase m) ∪ (((syntaxFormula0013).fv).erase m) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0176 freshnessCertificate0194))
  have freshnessCertificate0196 : n ∉ (syntaxFormula0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0195)
  have freshnessCertificate0197 : n ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ k from (by exact fresh_n_ne_k)))))
  have freshnessCertificate0198 : n ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0197 freshnessCertificate0029))
  have freshnessCertificate0199 : n ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0198)
  have freshnessCertificate0200 : n ∉ ((syn_cpw1 (.cv e))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0177)
  have freshnessCertificate0201 : n ∉ (((syn_cpw1 (.cv e))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0200 freshnessCertificate0197))
  have freshnessCertificate0202 : n ∉ ((Wff.classMem (syn_cpw1 (.cv e)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0201)
  have freshnessCertificate0203 : n ∉ ((syn_cpw1 (.cv f))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0185)
  have freshnessCertificate0204 : n ∉ (((syn_cpw1 (.cv f))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0203 freshnessCertificate0197))
  have freshnessCertificate0205 : n ∉ ((Wff.classMem (syn_cpw1 (.cv f)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0204)
  have freshnessCertificate0206 :
    n ∉
      (((Wff.classMem (syn_cpw1 (.cv e)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv f)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0202 freshnessCertificate0205))
  have freshnessCertificate0207 : n ∉ (syntaxFormula0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0206)
  have freshnessCertificate0208 : n ∉ ({ z, e } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show n ≠ z from (by exact fresh_n_ne_z)),
          (show n ≠ e from (by exact fresh_n_ne_e))⟩)
  have freshnessCertificate0209 : n ∉ ((Wff.objMem z e)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0208)
  have freshnessCertificate0210 : n ∉ ((Wff.neg (.objMem z e))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact freshnessCertificate0209)
  have freshnessCertificate0211 : n ∉ ({ w, f } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show n ≠ w from (by exact fresh_n_ne_w)),
          (show n ≠ f from (by exact fresh_n_ne_f))⟩)
  have freshnessCertificate0212 : n ∉ ((Wff.objMem w f)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0211)
  have freshnessCertificate0213 : n ∉ ((Wff.neg (.objMem w f))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact freshnessCertificate0212)
  have freshnessCertificate0214 :
    n ∉ (((Wff.neg (.objMem z e))).fv) ∪ (((Wff.neg (.objMem w f))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0210 freshnessCertificate0213))
  have freshnessCertificate0215 :
    n ∉ ((syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0214)
  have freshnessCertificate0216 :
    n ∉
      ((syntaxFormula0012).fv) ∪
        (((syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0207 freshnessCertificate0215))
  have freshnessCertificate0217 :
    n ∉
      ((syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0216)
  have freshnessCertificate0218 :
    n ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0199 freshnessCertificate0217))
  have freshnessCertificate0219 :
    n ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa syntaxFormula0012
            (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0218)
  have p0090 :=
    @g_rexlimdva
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (syn_wa (.objMem e n) (.objMem f n)) syntaxFormula0014 n (syn_cnnc)
      (by exact freshnessCertificate0196) (by exact freshnessCertificate0219) p0089
  have p0091 :=
    @g_syld
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (.all a (.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem e n) (.objMem f n))) syntaxFormula0014 p0069
      p0090
  have p0092 :=
    @g_imp
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (.all a (.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      syntaxFormula0014 p0091
  have p0093 :=
    @g_an32s (.classMem (.cv k) (syn_cnnc))
      (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f))))
      (.all a (.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      syntaxFormula0014 p0092
  have p0094 := @g_eleq1 (.cv c) (syn_cpw1 (.cv e)) (.cv k)
  have p0095_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv c) (syn_cpw1 (.cv e)))
        (syn_wb (.objMem c k) (.classMem (syn_cpw1 (.cv e)) (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa, syn_cpw,
          syn_wss, syn_c1c, syn_wex, syn_csn, syn_wb]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0094
  have p0095 :=
    @g_n_3ad2ant2 (.classEq (.cv c) (syn_cpw1 (.cv e)))
      (.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))
      (syn_wb (.objMem c k) (.classMem (syn_cpw1 (.cv e)) (.cv k)))
      (.classEq (.cv x) (syn_csn (.cv z))) p0095_e00_recanon
  have p0096 := @g_eleq1 (.cv d) (syn_cpw1 (.cv f)) (.cv k)
  have p0097_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv d) (syn_cpw1 (.cv f)))
        (syn_wb (.objMem d k) (.classMem (syn_cpw1 (.cv f)) (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa, syn_cpw,
          syn_wss, syn_c1c, syn_wex, syn_csn, syn_wb]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0096
  have p0097 :=
    @g_n_3ad2ant2 (.classEq (.cv d) (syn_cpw1 (.cv f)))
      (.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))
      (syn_wb (.objMem d k) (.classMem (syn_cpw1 (.cv f)) (.cv k)))
      (.classEq (.cv y) (syn_csn (.cv w))) p0097_e00_recanon
  have p0098 :=
    @g_bi2anan9 syntaxFormula0015 (.objMem c k) (.classMem (syn_cpw1 (.cv e)) (.cv k))
      syntaxFormula0016 (.objMem d k) (.classMem (syn_cpw1 (.cv f)) (.cv k)) p0095 p0097
  have p0099 := @g_compleq (.cv c) (syn_cpw1 (.cv e))
  have p0100 :=
    @g_eleq12 (.cv x) (syn_csn (.cv z)) (syn_ccompl (.cv c))
      (syn_ccompl (syn_cpw1 (.cv e)))
  have p0101 :=
    @g_sylan2 (.classEq (.cv c) (syn_cpw1 (.cv e))) (.classEq (.cv x) (syn_csn (.cv z)))
      (.classEq (syn_ccompl (.cv c)) (syn_ccompl (syn_cpw1 (.cv e))))
      (syn_wb (.classMem (.cv x) (syn_ccompl (.cv c)))
        (.classMem (syn_csn (.cv z)) (syn_ccompl (syn_cpw1 (.cv e)))))
      p0099 p0100
  have p0102 := @g_snex (.cv z)
  have p0103 := @g_elcompl (syn_csn (.cv z)) (syn_cpw1 (.cv e)) p0102
  have p0104 := @g_snelpw1 (.cv z) (.cv e)
  have p0105_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv e))) (.objMem z e)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_csn, syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan,
          syn_wa, syn_cpw, syn_wss, syn_c1c, syn_wex]
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
      p0104
  have p0105 :=
    @g_xchbinx (.classMem (syn_csn (.cv z)) (syn_ccompl (syn_cpw1 (.cv e))))
      (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv e))) (.objMem z e) p0103
      p0105_e01_recanon
  have p0106 :=
    @g_syl6bb
      (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv c) (syn_cpw1 (.cv e))))
      (.classMem (.cv x) (syn_ccompl (.cv c)))
      (.classMem (syn_csn (.cv z)) (syn_ccompl (syn_cpw1 (.cv e)))) (.neg (.objMem z e))
      p0101 p0105
  have p0107 :=
    @g_ancoms (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv c) (syn_cpw1 (.cv e)))
      (syn_wb (.classMem (.cv x) (syn_ccompl (.cv c))) (.neg (.objMem z e))) p0106
  have p0108 :=
    @g_n_3adant1 (.classEq (.cv c) (syn_cpw1 (.cv e)))
      (.classEq (.cv x) (syn_csn (.cv z)))
      (syn_wb (.classMem (.cv x) (syn_ccompl (.cv c))) (.neg (.objMem z e)))
      (.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z)))) p0107
  have p0109 := @g_compleq (.cv d) (syn_cpw1 (.cv f))
  have p0110 :=
    @g_eleq12 (.cv y) (syn_csn (.cv w)) (syn_ccompl (.cv d))
      (syn_ccompl (syn_cpw1 (.cv f)))
  have p0111 :=
    @g_sylan2 (.classEq (.cv d) (syn_cpw1 (.cv f))) (.classEq (.cv y) (syn_csn (.cv w)))
      (.classEq (syn_ccompl (.cv d)) (syn_ccompl (syn_cpw1 (.cv f))))
      (syn_wb (.classMem (.cv y) (syn_ccompl (.cv d)))
        (.classMem (syn_csn (.cv w)) (syn_ccompl (syn_cpw1 (.cv f)))))
      p0109 p0110
  have p0112 := @g_snex (.cv w)
  have p0113 := @g_elcompl (syn_csn (.cv w)) (syn_cpw1 (.cv f)) p0112
  have p0114 := @g_snelpw1 (.cv w) (.cv f)
  have p0115_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv w)) (syn_cpw1 (.cv f))) (.objMem w f)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_csn, syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan,
          syn_wa, syn_cpw, syn_wss, syn_c1c, syn_wex]
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
      p0114
  have p0115 :=
    @g_xchbinx (.classMem (syn_csn (.cv w)) (syn_ccompl (syn_cpw1 (.cv f))))
      (.classMem (syn_csn (.cv w)) (syn_cpw1 (.cv f))) (.objMem w f) p0113
      p0115_e01_recanon
  have p0116 :=
    @g_syl6bb
      (syn_wa (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv d) (syn_cpw1 (.cv f))))
      (.classMem (.cv y) (syn_ccompl (.cv d)))
      (.classMem (syn_csn (.cv w)) (syn_ccompl (syn_cpw1 (.cv f)))) (.neg (.objMem w f))
      p0111 p0115
  have p0117 :=
    @g_ancoms (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv d) (syn_cpw1 (.cv f)))
      (syn_wb (.classMem (.cv y) (syn_ccompl (.cv d))) (.neg (.objMem w f))) p0116
  have p0118 :=
    @g_n_3adant1 (.classEq (.cv d) (syn_cpw1 (.cv f)))
      (.classEq (.cv y) (syn_csn (.cv w)))
      (syn_wb (.classMem (.cv y) (syn_ccompl (.cv d))) (.neg (.objMem w f)))
      (.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w)))) p0117
  have p0119 :=
    @g_bi2anan9 syntaxFormula0015 (.classMem (.cv x) (syn_ccompl (.cv c)))
      (.neg (.objMem z e)) syntaxFormula0016 (.classMem (.cv y) (syn_ccompl (.cv d)))
      (.neg (.objMem w f)) p0108 p0118
  have p0120 :=
    @g_anbi12d syntaxFormula0017 (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0012
      syntaxFormula0018 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f))) p0098 p0119
  have p0121 :=
    @g_anbi2d syntaxFormula0017
      (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)
      (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
      p0120
  have p0122 := @g_eleq1 (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))) (.cv m)
  have p0123_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))
        (syn_wb (.objMem a m) (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl, syn_csn, syn_wb]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0122
  have p0123 :=
    @g_n_3ad2ant1 (.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))
      (.classEq (.cv c) (syn_cpw1 (.cv e)))
      (syn_wb (.objMem a m) (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (.cv m)))
      (.classEq (.cv x) (syn_csn (.cv z))) p0123_e00_recanon
  have p0124 := @g_eleq1 (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))) (.cv m)
  have p0125_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))
        (syn_wb (.objMem b m) (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl, syn_csn, syn_wb]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0124
  have p0125 :=
    @g_n_3ad2ant1 (.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))
      (.classEq (.cv d) (syn_cpw1 (.cv f)))
      (syn_wb (.objMem b m) (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (.cv m)))
      (.classEq (.cv y) (syn_csn (.cv w))) p0125_e00_recanon
  have p0126 :=
    @g_bi2anan9 syntaxFormula0015 (.objMem a m)
      (.classMem (syn_cun (.cv e) (syn_csn (.cv z))) (.cv m)) syntaxFormula0016
      (.objMem b m) (.classMem (syn_cun (.cv f) (syn_csn (.cv w))) (.cv m)) p0123 p0125
  have freshnessCertificate0220 : m ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ x from (by exact fresh_m_ne_x)))))
  have freshnessCertificate0221 : m ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0220 freshnessCertificate0162))
  have freshnessCertificate0222 : m ∉ ((Wff.classEq (.cv x) (syn_csn (.cv z)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0221)
  have freshnessCertificate0223 : m ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ a from (by exact fresh_m_ne_a)))))
  have freshnessCertificate0224 :
    m ∉ (((Class.cv a)).fv) ∪ (((syn_cun (.cv e) (syn_csn (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0223 freshnessCertificate0164))
  have freshnessCertificate0225 :
    m ∉ ((Wff.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0224)
  have freshnessCertificate0226 : m ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ c from (by exact fresh_m_ne_c)))))
  have freshnessCertificate0227 : m ∉ ((syn_cpw1 (.cv e))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0160)
  have freshnessCertificate0228 : m ∉ (((Class.cv c)).fv) ∪ (((syn_cpw1 (.cv e))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0226 freshnessCertificate0227))
  have freshnessCertificate0229 : m ∉ ((Wff.classEq (.cv c) (syn_cpw1 (.cv e)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0228)
  have freshnessCertificate0230 :
    m ∉
      (((Wff.classEq (.cv x) (syn_csn (.cv z)))).fv) ∪
          (((Wff.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))).fv) ∪
        (((Wff.classEq (.cv c) (syn_cpw1 (.cv e)))).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (by
          with_reducible
            exact
              (not_mem_support_union _ _ _ freshnessCertificate0222
                freshnessCertificate0225)) freshnessCertificate0229)
  have freshnessCertificate0231 : m ∉ (syntaxFormula0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a];
      exact freshnessCertificate0230)
  have freshnessCertificate0232 : m ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ y from (by exact fresh_m_ne_y)))))
  have freshnessCertificate0233 : m ∉ (((Class.cv y)).fv) ∪ (((syn_csn (.cv w))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0232 freshnessCertificate0169))
  have freshnessCertificate0234 : m ∉ ((Wff.classEq (.cv y) (syn_csn (.cv w)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0233)
  have freshnessCertificate0235 : m ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ b from (by exact fresh_m_ne_b)))))
  have freshnessCertificate0236 :
    m ∉ (((Class.cv b)).fv) ∪ (((syn_cun (.cv f) (syn_csn (.cv w)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0235 freshnessCertificate0171))
  have freshnessCertificate0237 :
    m ∉ ((Wff.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0236)
  have freshnessCertificate0238 : m ∉ ((Class.cv d)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ d } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ d from (by exact fresh_m_ne_d)))))
  have freshnessCertificate0239 : m ∉ ((syn_cpw1 (.cv f))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0167)
  have freshnessCertificate0240 : m ∉ (((Class.cv d)).fv) ∪ (((syn_cpw1 (.cv f))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0238 freshnessCertificate0239))
  have freshnessCertificate0241 : m ∉ ((Wff.classEq (.cv d) (syn_cpw1 (.cv f)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0240)
  have freshnessCertificate0242 :
    m ∉
      (((Wff.classEq (.cv y) (syn_csn (.cv w)))).fv) ∪
          (((Wff.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))).fv) ∪
        (((Wff.classEq (.cv d) (syn_cpw1 (.cv f)))).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (by
          with_reducible
            exact
              (not_mem_support_union _ _ _ freshnessCertificate0234
                freshnessCertificate0237)) freshnessCertificate0241)
  have freshnessCertificate0243 : m ∉ (syntaxFormula0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a];
      exact freshnessCertificate0242)
  have freshnessCertificate0244 :
    m ∉ ((syntaxFormula0015).fv) ∪ ((syntaxFormula0016).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0231 freshnessCertificate0243))
  have freshnessCertificate0245 : m ∉ (syntaxFormula0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0244)
  have p0127 :=
    @g_rexbidv syntaxFormula0017 (syn_wa (.objMem a m) (.objMem b m)) syntaxFormula0013 m
      (syn_cnnc) (by exact freshnessCertificate0245) p0126
  have p0128 :=
    @g_imbi12d syntaxFormula0017
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
        (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
        (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
      (syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m))) syntaxFormula0014 p0121
      p0127
  have p0129 :=
    @g_mpbiri syntaxFormula0017
      (.imp (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b
                (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))
        (syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m))))
      (.imp (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b
                (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa syntaxFormula0012 (syn_wa (.neg (.objMem z e)) (.neg (.objMem w f)))))
        syntaxFormula0014)
      p0093 p0128
  have p0130 :=
    @g_com12 syntaxFormula0017
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
        (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))
      (syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m))) p0129
  have freshnessCertificate0246 : z ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0247 : z ∉ (((syn_cnnc)).fv).erase m :=
    (fun hmem => freshnessCertificate0246 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0248 : z ∉ ({ a, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show z ≠ a from (by exact fresh_z_ne_a)),
          (show z ≠ m from (by exact fresh_z_ne_m))⟩)
  have freshnessCertificate0249 : z ∉ ((Wff.objMem a m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0248)
  have freshnessCertificate0250 : z ∉ ({ b, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show z ≠ b from (by exact fresh_z_ne_b)),
          (show z ≠ m from (by exact fresh_z_ne_m))⟩)
  have freshnessCertificate0251 : z ∉ ((Wff.objMem b m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0250)
  have freshnessCertificate0252 : z ∉ (((Wff.objMem a m)).fv) ∪ (((Wff.objMem b m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0249 freshnessCertificate0251))
  have freshnessCertificate0253 : z ∉ ((syn_wa (.objMem a m) (.objMem b m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0252)
  have freshnessCertificate0254 :
    z ∉ (((syn_wa (.objMem a m) (.objMem b m))).fv).erase m :=
    (fun hmem => freshnessCertificate0253 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0255 :
    z ∉
      ((((syn_cnnc)).fv).erase m) ∪
        ((((syn_wa (.objMem a m) (.objMem b m))).fv).erase m) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0247 freshnessCertificate0254))
  have freshnessCertificate0256 :
    z ∉ ((syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0255)
  have freshnessCertificate0257 : w ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0258 : w ∉ (((syn_cnnc)).fv).erase m :=
    (fun hmem => freshnessCertificate0257 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0259 : w ∉ ({ a, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show w ≠ a from (by exact fresh_w_ne_a)),
          (show w ≠ m from (by exact fresh_w_ne_m))⟩)
  have freshnessCertificate0260 : w ∉ ((Wff.objMem a m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0259)
  have freshnessCertificate0261 : w ∉ ({ b, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show w ≠ b from (by exact fresh_w_ne_b)),
          (show w ≠ m from (by exact fresh_w_ne_m))⟩)
  have freshnessCertificate0262 : w ∉ ((Wff.objMem b m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0261)
  have freshnessCertificate0263 : w ∉ (((Wff.objMem a m)).fv) ∪ (((Wff.objMem b m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0260 freshnessCertificate0262))
  have freshnessCertificate0264 : w ∉ ((syn_wa (.objMem a m) (.objMem b m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0263)
  have freshnessCertificate0265 :
    w ∉ (((syn_wa (.objMem a m) (.objMem b m))).fv).erase m :=
    (fun hmem => freshnessCertificate0264 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0266 :
    w ∉
      ((((syn_cnnc)).fv).erase m) ∪
        ((((syn_wa (.objMem a m) (.objMem b m))).fv).erase m) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0258 freshnessCertificate0265))
  have freshnessCertificate0267 :
    w ∉ ((syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0266)
  have freshnessCertificate0268 : z ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ k from (by exact fresh_z_ne_k)))))
  have freshnessCertificate0269 : z ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0268 freshnessCertificate0246))
  have freshnessCertificate0270 : z ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0269)
  have freshnessCertificate0271 : z ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ a from (by exact fresh_z_ne_a)))))
  have freshnessCertificate0272 : z ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0271)
  have freshnessCertificate0273 : z ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0272 freshnessCertificate0268))
  have freshnessCertificate0274 : z ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0273)
  have freshnessCertificate0275 : z ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ b from (by exact fresh_z_ne_b)))))
  have freshnessCertificate0276 : z ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0275)
  have freshnessCertificate0277 : z ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0276 freshnessCertificate0268))
  have freshnessCertificate0278 : z ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0277)
  have freshnessCertificate0279 :
    z ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0274 freshnessCertificate0278))
  have freshnessCertificate0280 : z ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0279)
  have freshnessCertificate0281 : z ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0246 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0282 : z ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show z ≠ a from (by exact fresh_z_ne_a)),
          (show z ≠ n from (by exact fresh_z_ne_n))⟩)
  have freshnessCertificate0283 : z ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0282)
  have freshnessCertificate0284 : z ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show z ≠ b from (by exact fresh_z_ne_b)),
          (show z ≠ n from (by exact fresh_z_ne_n))⟩)
  have freshnessCertificate0285 : z ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0284)
  have freshnessCertificate0286 : z ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0283 freshnessCertificate0285))
  have freshnessCertificate0287 : z ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0286)
  have freshnessCertificate0288 :
    z ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0287 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0289 :
    z ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0281 freshnessCertificate0288))
  have freshnessCertificate0290 :
    z ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0289)
  have freshnessCertificate0291 :
    z ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0280 freshnessCertificate0290))
  have freshnessCertificate0292 :
    z ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0291)
  have freshnessCertificate0293 :
    z ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0292 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0294 :
    z ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0293)
  have freshnessCertificate0295 :
    z ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0294 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0296 :
    z ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0295)
  have freshnessCertificate0297 :
    z ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((Wff.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0270 freshnessCertificate0296))
  have freshnessCertificate0298 :
    z ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0297)
  have freshnessCertificate0299 : z ∉ ({ c, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show z ≠ c from (by exact fresh_z_ne_c)),
          (show z ≠ k from (by exact fresh_z_ne_k))⟩)
  have freshnessCertificate0300 : z ∉ ((Wff.objMem c k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0299)
  have freshnessCertificate0301 : z ∉ ({ d, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show z ≠ d from (by exact fresh_z_ne_d)),
          (show z ≠ k from (by exact fresh_z_ne_k))⟩)
  have freshnessCertificate0302 : z ∉ ((Wff.objMem d k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0301)
  have freshnessCertificate0303 : z ∉ (((Wff.objMem c k)).fv) ∪ (((Wff.objMem d k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0300 freshnessCertificate0302))
  have freshnessCertificate0304 : z ∉ ((syn_wa (.objMem c k) (.objMem d k))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0303)
  have freshnessCertificate0305 : z ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ x from (by exact fresh_z_ne_x)))))
  have freshnessCertificate0306 : z ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ c from (by exact fresh_z_ne_c)))))
  have freshnessCertificate0307 : z ∉ ((syn_ccompl (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0306)
  have freshnessCertificate0308 : z ∉ (((Class.cv x)).fv) ∪ (((syn_ccompl (.cv c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0305 freshnessCertificate0307))
  have freshnessCertificate0309 : z ∉ ((Wff.classMem (.cv x) (syn_ccompl (.cv c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0308)
  have freshnessCertificate0310 : z ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ y from (by exact fresh_z_ne_y)))))
  have freshnessCertificate0311 : z ∉ ((Class.cv d)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ d } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ d from (by exact fresh_z_ne_d)))))
  have freshnessCertificate0312 : z ∉ ((syn_ccompl (.cv d))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0311)
  have freshnessCertificate0313 : z ∉ (((Class.cv y)).fv) ∪ (((syn_ccompl (.cv d))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0310 freshnessCertificate0312))
  have freshnessCertificate0314 : z ∉ ((Wff.classMem (.cv y) (syn_ccompl (.cv d)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0313)
  have freshnessCertificate0315 :
    z ∉
      (((Wff.classMem (.cv x) (syn_ccompl (.cv c)))).fv) ∪
        (((Wff.classMem (.cv y) (syn_ccompl (.cv d)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0309 freshnessCertificate0314))
  have freshnessCertificate0316 : z ∉ (syntaxFormula0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0315)
  have freshnessCertificate0317 :
    z ∉ (((syn_wa (.objMem c k) (.objMem d k))).fv) ∪ ((syntaxFormula0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0304 freshnessCertificate0316))
  have freshnessCertificate0318 :
    z ∉ ((syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0317)
  have freshnessCertificate0319 :
    z ∉
      (((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv) ∪
        (((syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0298 freshnessCertificate0318))
  have freshnessCertificate0320 :
    z ∉
      ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0319)
  have freshnessCertificate0321 : w ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ k from (by exact fresh_w_ne_k)))))
  have freshnessCertificate0322 : w ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0321 freshnessCertificate0257))
  have freshnessCertificate0323 : w ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0322)
  have freshnessCertificate0324 : w ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ a from (by exact fresh_w_ne_a)))))
  have freshnessCertificate0325 : w ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0324)
  have freshnessCertificate0326 : w ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0325 freshnessCertificate0321))
  have freshnessCertificate0327 : w ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0326)
  have freshnessCertificate0328 : w ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ b from (by exact fresh_w_ne_b)))))
  have freshnessCertificate0329 : w ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0328)
  have freshnessCertificate0330 : w ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0329 freshnessCertificate0321))
  have freshnessCertificate0331 : w ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0330)
  have freshnessCertificate0332 :
    w ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0327 freshnessCertificate0331))
  have freshnessCertificate0333 : w ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0332)
  have freshnessCertificate0334 : w ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0257 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0335 : w ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show w ≠ a from (by exact fresh_w_ne_a)),
          (show w ≠ n from (by exact fresh_w_ne_n))⟩)
  have freshnessCertificate0336 : w ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0335)
  have freshnessCertificate0337 : w ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show w ≠ b from (by exact fresh_w_ne_b)),
          (show w ≠ n from (by exact fresh_w_ne_n))⟩)
  have freshnessCertificate0338 : w ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0337)
  have freshnessCertificate0339 : w ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0336 freshnessCertificate0338))
  have freshnessCertificate0340 : w ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0339)
  have freshnessCertificate0341 :
    w ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0340 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0342 :
    w ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0334 freshnessCertificate0341))
  have freshnessCertificate0343 :
    w ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0342)
  have freshnessCertificate0344 :
    w ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0333 freshnessCertificate0343))
  have freshnessCertificate0345 :
    w ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0344)
  have freshnessCertificate0346 :
    w ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0345 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0347 :
    w ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0346)
  have freshnessCertificate0348 :
    w ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0347 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0349 :
    w ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0348)
  have freshnessCertificate0350 :
    w ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((Wff.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0323 freshnessCertificate0349))
  have freshnessCertificate0351 :
    w ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0350)
  have freshnessCertificate0352 : w ∉ ({ c, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show w ≠ c from (by exact fresh_w_ne_c)),
          (show w ≠ k from (by exact fresh_w_ne_k))⟩)
  have freshnessCertificate0353 : w ∉ ((Wff.objMem c k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0352)
  have freshnessCertificate0354 : w ∉ ({ d, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show w ≠ d from (by exact fresh_w_ne_d)),
          (show w ≠ k from (by exact fresh_w_ne_k))⟩)
  have freshnessCertificate0355 : w ∉ ((Wff.objMem d k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0354)
  have freshnessCertificate0356 : w ∉ (((Wff.objMem c k)).fv) ∪ (((Wff.objMem d k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0353 freshnessCertificate0355))
  have freshnessCertificate0357 : w ∉ ((syn_wa (.objMem c k) (.objMem d k))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0356)
  have freshnessCertificate0358 : w ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ x from (by exact fresh_w_ne_x)))))
  have freshnessCertificate0359 : w ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ c from (by exact fresh_w_ne_c)))))
  have freshnessCertificate0360 : w ∉ ((syn_ccompl (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0359)
  have freshnessCertificate0361 : w ∉ (((Class.cv x)).fv) ∪ (((syn_ccompl (.cv c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0358 freshnessCertificate0360))
  have freshnessCertificate0362 : w ∉ ((Wff.classMem (.cv x) (syn_ccompl (.cv c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0361)
  have freshnessCertificate0363 : w ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ y from (by exact fresh_w_ne_y)))))
  have freshnessCertificate0364 : w ∉ ((Class.cv d)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ d } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ d from (by exact fresh_w_ne_d)))))
  have freshnessCertificate0365 : w ∉ ((syn_ccompl (.cv d))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0364)
  have freshnessCertificate0366 : w ∉ (((Class.cv y)).fv) ∪ (((syn_ccompl (.cv d))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0363 freshnessCertificate0365))
  have freshnessCertificate0367 : w ∉ ((Wff.classMem (.cv y) (syn_ccompl (.cv d)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0366)
  have freshnessCertificate0368 :
    w ∉
      (((Wff.classMem (.cv x) (syn_ccompl (.cv c)))).fv) ∪
        (((Wff.classMem (.cv y) (syn_ccompl (.cv d)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0362 freshnessCertificate0367))
  have freshnessCertificate0369 : w ∉ (syntaxFormula0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0368)
  have freshnessCertificate0370 :
    w ∉ (((syn_wa (.objMem c k) (.objMem d k))).fv) ∪ ((syntaxFormula0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0357 freshnessCertificate0369))
  have freshnessCertificate0371 :
    w ∉ ((syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0370)
  have freshnessCertificate0372 :
    w ∉
      (((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv) ∪
        (((syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0351 freshnessCertificate0371))
  have freshnessCertificate0373 :
    w ∉
      ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0372)
  have p0131 :=
    @g_exlimdvv
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
        (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))
      syntaxFormula0017 (syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m))) z w
      (by exact freshnessCertificate0256) (by exact freshnessCertificate0267)
      (by exact freshnessCertificate0320) (by exact freshnessCertificate0373) p0130
  have freshnessCertificate0374 : e ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show e ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0375 : e ∉ (((syn_cnnc)).fv).erase m :=
    (fun hmem => freshnessCertificate0374 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0376 : e ∉ ({ a, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show e ≠ a from (by exact fresh_e_ne_a)),
          (show e ≠ m from (by exact fresh_e_ne_m))⟩)
  have freshnessCertificate0377 : e ∉ ((Wff.objMem a m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0376)
  have freshnessCertificate0378 : e ∉ ({ b, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show e ≠ b from (by exact fresh_e_ne_b)),
          (show e ≠ m from (by exact fresh_e_ne_m))⟩)
  have freshnessCertificate0379 : e ∉ ((Wff.objMem b m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0378)
  have freshnessCertificate0380 : e ∉ (((Wff.objMem a m)).fv) ∪ (((Wff.objMem b m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0377 freshnessCertificate0379))
  have freshnessCertificate0381 : e ∉ ((syn_wa (.objMem a m) (.objMem b m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0380)
  have freshnessCertificate0382 :
    e ∉ (((syn_wa (.objMem a m) (.objMem b m))).fv).erase m :=
    (fun hmem => freshnessCertificate0381 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0383 :
    e ∉
      ((((syn_cnnc)).fv).erase m) ∪
        ((((syn_wa (.objMem a m) (.objMem b m))).fv).erase m) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0375 freshnessCertificate0382))
  have freshnessCertificate0384 :
    e ∉ ((syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0383)
  have freshnessCertificate0385 : f ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show f ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0386 : f ∉ (((syn_cnnc)).fv).erase m :=
    (fun hmem => freshnessCertificate0385 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0387 : f ∉ ({ a, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show f ≠ a from (by exact fresh_f_ne_a)),
          (show f ≠ m from (by exact fresh_f_ne_m))⟩)
  have freshnessCertificate0388 : f ∉ ((Wff.objMem a m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0387)
  have freshnessCertificate0389 : f ∉ ({ b, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show f ≠ b from (by exact fresh_f_ne_b)),
          (show f ≠ m from (by exact fresh_f_ne_m))⟩)
  have freshnessCertificate0390 : f ∉ ((Wff.objMem b m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0389)
  have freshnessCertificate0391 : f ∉ (((Wff.objMem a m)).fv) ∪ (((Wff.objMem b m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0388 freshnessCertificate0390))
  have freshnessCertificate0392 : f ∉ ((syn_wa (.objMem a m) (.objMem b m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0391)
  have freshnessCertificate0393 :
    f ∉ (((syn_wa (.objMem a m) (.objMem b m))).fv).erase m :=
    (fun hmem => freshnessCertificate0392 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0394 :
    f ∉
      ((((syn_cnnc)).fv).erase m) ∪
        ((((syn_wa (.objMem a m) (.objMem b m))).fv).erase m) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0386 freshnessCertificate0393))
  have freshnessCertificate0395 :
    f ∉ ((syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0394)
  have freshnessCertificate0396 : e ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ k from (by exact fresh_e_ne_k)))))
  have freshnessCertificate0397 : e ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0396 freshnessCertificate0374))
  have freshnessCertificate0398 : e ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0397)
  have freshnessCertificate0399 : e ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ a from (by exact fresh_e_ne_a)))))
  have freshnessCertificate0400 : e ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0399)
  have freshnessCertificate0401 : e ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0400 freshnessCertificate0396))
  have freshnessCertificate0402 : e ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0401)
  have freshnessCertificate0403 : e ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ b from (by exact fresh_e_ne_b)))))
  have freshnessCertificate0404 : e ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0403)
  have freshnessCertificate0405 : e ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0404 freshnessCertificate0396))
  have freshnessCertificate0406 : e ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0405)
  have freshnessCertificate0407 :
    e ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0402 freshnessCertificate0406))
  have freshnessCertificate0408 : e ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0407)
  have freshnessCertificate0409 : e ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0374 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0410 : e ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show e ≠ a from (by exact fresh_e_ne_a)),
          (show e ≠ n from (by exact fresh_e_ne_n))⟩)
  have freshnessCertificate0411 : e ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0410)
  have freshnessCertificate0412 : e ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show e ≠ b from (by exact fresh_e_ne_b)),
          (show e ≠ n from (by exact fresh_e_ne_n))⟩)
  have freshnessCertificate0413 : e ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0412)
  have freshnessCertificate0414 : e ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0411 freshnessCertificate0413))
  have freshnessCertificate0415 : e ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0414)
  have freshnessCertificate0416 :
    e ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0415 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0417 :
    e ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0409 freshnessCertificate0416))
  have freshnessCertificate0418 :
    e ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0417)
  have freshnessCertificate0419 :
    e ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0408 freshnessCertificate0418))
  have freshnessCertificate0420 :
    e ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0419)
  have freshnessCertificate0421 :
    e ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0420 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0422 :
    e ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0421)
  have freshnessCertificate0423 :
    e ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0422 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0424 :
    e ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0423)
  have freshnessCertificate0425 :
    e ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((Wff.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0398 freshnessCertificate0424))
  have freshnessCertificate0426 :
    e ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0425)
  have freshnessCertificate0427 : e ∉ ({ c, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show e ≠ c from (by exact fresh_e_ne_c)),
          (show e ≠ k from (by exact fresh_e_ne_k))⟩)
  have freshnessCertificate0428 : e ∉ ((Wff.objMem c k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0427)
  have freshnessCertificate0429 : e ∉ ({ d, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show e ≠ d from (by exact fresh_e_ne_d)),
          (show e ≠ k from (by exact fresh_e_ne_k))⟩)
  have freshnessCertificate0430 : e ∉ ((Wff.objMem d k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0429)
  have freshnessCertificate0431 : e ∉ (((Wff.objMem c k)).fv) ∪ (((Wff.objMem d k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0428 freshnessCertificate0430))
  have freshnessCertificate0432 : e ∉ ((syn_wa (.objMem c k) (.objMem d k))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0431)
  have freshnessCertificate0433 : e ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ x from (by exact fresh_e_ne_x)))))
  have freshnessCertificate0434 : e ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ c from (by exact fresh_e_ne_c)))))
  have freshnessCertificate0435 : e ∉ ((syn_ccompl (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0434)
  have freshnessCertificate0436 : e ∉ (((Class.cv x)).fv) ∪ (((syn_ccompl (.cv c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0433 freshnessCertificate0435))
  have freshnessCertificate0437 : e ∉ ((Wff.classMem (.cv x) (syn_ccompl (.cv c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0436)
  have freshnessCertificate0438 : e ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ y from (by exact fresh_e_ne_y)))))
  have freshnessCertificate0439 : e ∉ ((Class.cv d)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ d } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ d from (by exact fresh_e_ne_d)))))
  have freshnessCertificate0440 : e ∉ ((syn_ccompl (.cv d))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0439)
  have freshnessCertificate0441 : e ∉ (((Class.cv y)).fv) ∪ (((syn_ccompl (.cv d))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0438 freshnessCertificate0440))
  have freshnessCertificate0442 : e ∉ ((Wff.classMem (.cv y) (syn_ccompl (.cv d)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0441)
  have freshnessCertificate0443 :
    e ∉
      (((Wff.classMem (.cv x) (syn_ccompl (.cv c)))).fv) ∪
        (((Wff.classMem (.cv y) (syn_ccompl (.cv d)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0437 freshnessCertificate0442))
  have freshnessCertificate0444 : e ∉ (syntaxFormula0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0443)
  have freshnessCertificate0445 :
    e ∉ (((syn_wa (.objMem c k) (.objMem d k))).fv) ∪ ((syntaxFormula0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0432 freshnessCertificate0444))
  have freshnessCertificate0446 :
    e ∉ ((syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0445)
  have freshnessCertificate0447 :
    e ∉
      (((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv) ∪
        (((syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0426 freshnessCertificate0446))
  have freshnessCertificate0448 :
    e ∉
      ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0447)
  have freshnessCertificate0449 : f ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ k from (by exact fresh_f_ne_k)))))
  have freshnessCertificate0450 : f ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0449 freshnessCertificate0385))
  have freshnessCertificate0451 : f ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0450)
  have freshnessCertificate0452 : f ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ a from (by exact fresh_f_ne_a)))))
  have freshnessCertificate0453 : f ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0452)
  have freshnessCertificate0454 : f ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0453 freshnessCertificate0449))
  have freshnessCertificate0455 : f ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0454)
  have freshnessCertificate0456 : f ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ b from (by exact fresh_f_ne_b)))))
  have freshnessCertificate0457 : f ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0456)
  have freshnessCertificate0458 : f ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0457 freshnessCertificate0449))
  have freshnessCertificate0459 : f ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0458)
  have freshnessCertificate0460 :
    f ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0455 freshnessCertificate0459))
  have freshnessCertificate0461 : f ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0460)
  have freshnessCertificate0462 : f ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0385 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0463 : f ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show f ≠ a from (by exact fresh_f_ne_a)),
          (show f ≠ n from (by exact fresh_f_ne_n))⟩)
  have freshnessCertificate0464 : f ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0463)
  have freshnessCertificate0465 : f ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show f ≠ b from (by exact fresh_f_ne_b)),
          (show f ≠ n from (by exact fresh_f_ne_n))⟩)
  have freshnessCertificate0466 : f ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0465)
  have freshnessCertificate0467 : f ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0464 freshnessCertificate0466))
  have freshnessCertificate0468 : f ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0467)
  have freshnessCertificate0469 :
    f ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0468 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0470 :
    f ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0462 freshnessCertificate0469))
  have freshnessCertificate0471 :
    f ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0470)
  have freshnessCertificate0472 :
    f ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0461 freshnessCertificate0471))
  have freshnessCertificate0473 :
    f ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0472)
  have freshnessCertificate0474 :
    f ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0473 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0475 :
    f ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0474)
  have freshnessCertificate0476 :
    f ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0475 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0477 :
    f ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0476)
  have freshnessCertificate0478 :
    f ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((Wff.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0451 freshnessCertificate0477))
  have freshnessCertificate0479 :
    f ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0478)
  have freshnessCertificate0480 : f ∉ ({ c, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show f ≠ c from (by exact fresh_f_ne_c)),
          (show f ≠ k from (by exact fresh_f_ne_k))⟩)
  have freshnessCertificate0481 : f ∉ ((Wff.objMem c k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0480)
  have freshnessCertificate0482 : f ∉ ({ d, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show f ≠ d from (by exact fresh_f_ne_d)),
          (show f ≠ k from (by exact fresh_f_ne_k))⟩)
  have freshnessCertificate0483 : f ∉ ((Wff.objMem d k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0482)
  have freshnessCertificate0484 : f ∉ (((Wff.objMem c k)).fv) ∪ (((Wff.objMem d k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0481 freshnessCertificate0483))
  have freshnessCertificate0485 : f ∉ ((syn_wa (.objMem c k) (.objMem d k))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0484)
  have freshnessCertificate0486 : f ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ x from (by exact fresh_f_ne_x)))))
  have freshnessCertificate0487 : f ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ c from (by exact fresh_f_ne_c)))))
  have freshnessCertificate0488 : f ∉ ((syn_ccompl (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0487)
  have freshnessCertificate0489 : f ∉ (((Class.cv x)).fv) ∪ (((syn_ccompl (.cv c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0486 freshnessCertificate0488))
  have freshnessCertificate0490 : f ∉ ((Wff.classMem (.cv x) (syn_ccompl (.cv c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0489)
  have freshnessCertificate0491 : f ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ y from (by exact fresh_f_ne_y)))))
  have freshnessCertificate0492 : f ∉ ((Class.cv d)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ d } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ d from (by exact fresh_f_ne_d)))))
  have freshnessCertificate0493 : f ∉ ((syn_ccompl (.cv d))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0492)
  have freshnessCertificate0494 : f ∉ (((Class.cv y)).fv) ∪ (((syn_ccompl (.cv d))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0491 freshnessCertificate0493))
  have freshnessCertificate0495 : f ∉ ((Wff.classMem (.cv y) (syn_ccompl (.cv d)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0494)
  have freshnessCertificate0496 :
    f ∉
      (((Wff.classMem (.cv x) (syn_ccompl (.cv c)))).fv) ∪
        (((Wff.classMem (.cv y) (syn_ccompl (.cv d)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0490 freshnessCertificate0495))
  have freshnessCertificate0497 : f ∉ (syntaxFormula0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0496)
  have freshnessCertificate0498 :
    f ∉ (((syn_wa (.objMem c k) (.objMem d k))).fv) ∪ ((syntaxFormula0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0485 freshnessCertificate0497))
  have freshnessCertificate0499 :
    f ∉ ((syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0498)
  have freshnessCertificate0500 :
    f ∉
      (((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv) ∪
        (((syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0479 freshnessCertificate0499))
  have freshnessCertificate0501 :
    f ∉
      ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0500)
  have p0132 :=
    @g_exlimdvv
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
        (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))
      syntaxFormula0020 (syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m))) e f
      (by exact freshnessCertificate0384) (by exact freshnessCertificate0395)
      (by exact freshnessCertificate0448) (by exact freshnessCertificate0501) p0131
  have freshnessCertificate0502 : f ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ z from (by exact fresh_f_ne_z)))))
  have freshnessCertificate0503 : f ∉ ((syn_csn (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0502)
  have freshnessCertificate0504 : f ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0486 freshnessCertificate0503))
  have freshnessCertificate0505 : f ∉ ((Wff.classEq (.cv x) (syn_csn (.cv z)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0504)
  have freshnessCertificate0506 : f ∉ ((Class.cv e)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show f ∉ ({ e } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show f ≠ e from (by exact fresh_f_ne_e)))))
  have freshnessCertificate0507 : f ∉ (((Class.cv e)).fv) ∪ (((syn_csn (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0506 freshnessCertificate0503))
  have freshnessCertificate0508 : f ∉ ((syn_cun (.cv e) (syn_csn (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0507)
  have freshnessCertificate0509 :
    f ∉ (((Class.cv a)).fv) ∪ (((syn_cun (.cv e) (syn_csn (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0452 freshnessCertificate0508))
  have freshnessCertificate0510 :
    f ∉ ((Wff.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0509)
  have freshnessCertificate0511 : f ∉ ((syn_cpw1 (.cv e))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0506)
  have freshnessCertificate0512 : f ∉ (((Class.cv c)).fv) ∪ (((syn_cpw1 (.cv e))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0487 freshnessCertificate0511))
  have freshnessCertificate0513 : f ∉ ((Wff.classEq (.cv c) (syn_cpw1 (.cv e)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0512)
  have freshnessCertificate0514 :
    f ∉
      (((Wff.classEq (.cv x) (syn_csn (.cv z)))).fv) ∪
          (((Wff.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))).fv) ∪
        (((Wff.classEq (.cv c) (syn_cpw1 (.cv e)))).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (by
          with_reducible
            exact
              (not_mem_support_union _ _ _ freshnessCertificate0505
                freshnessCertificate0510)) freshnessCertificate0513)
  have freshnessCertificate0515 : f ∉ (syntaxFormula0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a];
      exact freshnessCertificate0514)
  have freshnessCertificate0516 : f ∉ ((syntaxFormula0015).fv).erase z :=
    (fun hmem => freshnessCertificate0515 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0517 : f ∉ (syntaxFormula0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex];
      exact freshnessCertificate0516)
  have freshnessCertificate0518 : e ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ w from (by exact fresh_e_ne_w)))))
  have freshnessCertificate0519 : e ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0518)
  have freshnessCertificate0520 : e ∉ (((Class.cv y)).fv) ∪ (((syn_csn (.cv w))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0438 freshnessCertificate0519))
  have freshnessCertificate0521 : e ∉ ((Wff.classEq (.cv y) (syn_csn (.cv w)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0520)
  have freshnessCertificate0522 : e ∉ ((Class.cv f)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ f } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ f from (by exact fresh_e_ne_f)))))
  have freshnessCertificate0523 : e ∉ (((Class.cv f)).fv) ∪ (((syn_csn (.cv w))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0522 freshnessCertificate0519))
  have freshnessCertificate0524 : e ∉ ((syn_cun (.cv f) (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0523)
  have freshnessCertificate0525 :
    e ∉ (((Class.cv b)).fv) ∪ (((syn_cun (.cv f) (syn_csn (.cv w)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0403 freshnessCertificate0524))
  have freshnessCertificate0526 :
    e ∉ ((Wff.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0525)
  have freshnessCertificate0527 : e ∉ ((syn_cpw1 (.cv f))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0522)
  have freshnessCertificate0528 : e ∉ (((Class.cv d)).fv) ∪ (((syn_cpw1 (.cv f))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0439 freshnessCertificate0527))
  have freshnessCertificate0529 : e ∉ ((Wff.classEq (.cv d) (syn_cpw1 (.cv f)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0528)
  have freshnessCertificate0530 :
    e ∉
      (((Wff.classEq (.cv y) (syn_csn (.cv w)))).fv) ∪
          (((Wff.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))).fv) ∪
        (((Wff.classEq (.cv d) (syn_cpw1 (.cv f)))).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (by
          with_reducible
            exact
              (not_mem_support_union _ _ _ freshnessCertificate0521
                freshnessCertificate0526)) freshnessCertificate0529)
  have freshnessCertificate0531 : e ∉ (syntaxFormula0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a];
      exact freshnessCertificate0530)
  have freshnessCertificate0532 : e ∉ ((syntaxFormula0016).fv).erase w :=
    (fun hmem => freshnessCertificate0531 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0533 : e ∉ (syntaxFormula0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex];
      exact freshnessCertificate0532)
  have p0133 :=
    @g_eeanv syntaxFormula0021 syntaxFormula0022 e f (by exact freshnessCertificate0517)
      (by exact freshnessCertificate0533)
  have freshnessCertificate0534 : w ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ z from (by exact fresh_w_ne_z)))))
  have freshnessCertificate0535 : w ∉ ((syn_csn (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0534)
  have freshnessCertificate0536 : w ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0358 freshnessCertificate0535))
  have freshnessCertificate0537 : w ∉ ((Wff.classEq (.cv x) (syn_csn (.cv z)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0536)
  have freshnessCertificate0538 : w ∉ ((Class.cv e)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ e } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ e from (by exact fresh_w_ne_e)))))
  have freshnessCertificate0539 : w ∉ (((Class.cv e)).fv) ∪ (((syn_csn (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0538 freshnessCertificate0535))
  have freshnessCertificate0540 : w ∉ ((syn_cun (.cv e) (syn_csn (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0539)
  have freshnessCertificate0541 :
    w ∉ (((Class.cv a)).fv) ∪ (((syn_cun (.cv e) (syn_csn (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0324 freshnessCertificate0540))
  have freshnessCertificate0542 :
    w ∉ ((Wff.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0541)
  have freshnessCertificate0543 : w ∉ ((syn_cpw1 (.cv e))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0538)
  have freshnessCertificate0544 : w ∉ (((Class.cv c)).fv) ∪ (((syn_cpw1 (.cv e))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0359 freshnessCertificate0543))
  have freshnessCertificate0545 : w ∉ ((Wff.classEq (.cv c) (syn_cpw1 (.cv e)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0544)
  have freshnessCertificate0546 :
    w ∉
      (((Wff.classEq (.cv x) (syn_csn (.cv z)))).fv) ∪
          (((Wff.classEq (.cv a) (syn_cun (.cv e) (syn_csn (.cv z))))).fv) ∪
        (((Wff.classEq (.cv c) (syn_cpw1 (.cv e)))).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (by
          with_reducible
            exact
              (not_mem_support_union _ _ _ freshnessCertificate0537
                freshnessCertificate0542)) freshnessCertificate0545)
  have freshnessCertificate0547 : w ∉ (syntaxFormula0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a];
      exact freshnessCertificate0546)
  have freshnessCertificate0548 : z ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ w from (by exact fresh_z_ne_w)))))
  have freshnessCertificate0549 : z ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0548)
  have freshnessCertificate0550 : z ∉ (((Class.cv y)).fv) ∪ (((syn_csn (.cv w))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0310 freshnessCertificate0549))
  have freshnessCertificate0551 : z ∉ ((Wff.classEq (.cv y) (syn_csn (.cv w)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0550)
  have freshnessCertificate0552 : z ∉ ((Class.cv f)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ f } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ f from (by exact fresh_z_ne_f)))))
  have freshnessCertificate0553 : z ∉ (((Class.cv f)).fv) ∪ (((syn_csn (.cv w))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0552 freshnessCertificate0549))
  have freshnessCertificate0554 : z ∉ ((syn_cun (.cv f) (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0553)
  have freshnessCertificate0555 :
    z ∉ (((Class.cv b)).fv) ∪ (((syn_cun (.cv f) (syn_csn (.cv w)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0275 freshnessCertificate0554))
  have freshnessCertificate0556 :
    z ∉ ((Wff.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0555)
  have freshnessCertificate0557 : z ∉ ((syn_cpw1 (.cv f))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0552)
  have freshnessCertificate0558 : z ∉ (((Class.cv d)).fv) ∪ (((syn_cpw1 (.cv f))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0311 freshnessCertificate0557))
  have freshnessCertificate0559 : z ∉ ((Wff.classEq (.cv d) (syn_cpw1 (.cv f)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0558)
  have freshnessCertificate0560 :
    z ∉
      (((Wff.classEq (.cv y) (syn_csn (.cv w)))).fv) ∪
          (((Wff.classEq (.cv b) (syn_cun (.cv f) (syn_csn (.cv w))))).fv) ∪
        (((Wff.classEq (.cv d) (syn_cpw1 (.cv f)))).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (by
          with_reducible
            exact
              (not_mem_support_union _ _ _ freshnessCertificate0551
                freshnessCertificate0556)) freshnessCertificate0559)
  have freshnessCertificate0561 : z ∉ (syntaxFormula0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a];
      exact freshnessCertificate0560)
  have p0134 :=
    @g_eeanv syntaxFormula0015 syntaxFormula0016 z w (by exact freshnessCertificate0547)
      (by exact freshnessCertificate0561)
  have p0135 := @g_n_2exbii syntaxFormula0020 syntaxFormula0023 e f p0134
  have p0136 := @g_vex c
  have p0137 := @g_vex x
  have p0138 :=
    @g_pw1eqadj e z (.cv c) (.cv x) (.cv a) (by exact freshnessCertificate0434)
      (by exact freshnessCertificate0306) (by exact freshnessCertificate0433)
      (by exact freshnessCertificate0305) (by exact freshnessCertificate0399)
      (by exact freshnessCertificate0271) (show e ≠ z from (by exact fresh_e_ne_z)) p0136
      p0137
  have p0139 := @g_vex d
  have p0140 := @g_vex y
  have p0141 :=
    @g_pw1eqadj f w (.cv d) (.cv y) (.cv b) (by exact freshnessCertificate0492)
      (by exact freshnessCertificate0364) (by exact freshnessCertificate0491)
      (by exact freshnessCertificate0363) (by exact freshnessCertificate0456)
      (by exact freshnessCertificate0328) (show f ≠ w from (by exact fresh_f_ne_w)) p0139
      p0140
  have p0142 :=
    @g_anbi12i (.classEq (syn_cpw1 (.cv a)) (syn_cun (.cv c) (syn_csn (.cv x))))
      (syn_wex e syntaxFormula0021)
      (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv d) (syn_csn (.cv y))))
      (syn_wex f syntaxFormula0022) p0138 p0141
  have p0143 :=
    @g_n_3bitr4ri (syn_wex e (syn_wex f syntaxFormula0023))
      (syn_wa (syn_wex e syntaxFormula0021) (syn_wex f syntaxFormula0022))
      syntaxFormula0025 syntaxFormula0006 p0133 p0135 p0142
  have p0144 := @g_elequ2 n m a
  have p0145 := @g_elequ2 n m b
  have p0146 :=
    @g_anbi12d (.objEq n m) (.objMem a n) (.objMem a m) (.objMem b n) (.objMem b m) p0144
      p0145
  have freshnessCertificate0562 : m ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show m ≠ a from (by exact fresh_m_ne_a)),
          (show m ≠ n from (by exact fresh_m_ne_n))⟩)
  have freshnessCertificate0563 : m ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0562)
  have freshnessCertificate0564 : m ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show m ≠ b from (by exact fresh_m_ne_b)),
          (show m ≠ n from (by exact fresh_m_ne_n))⟩)
  have freshnessCertificate0565 : m ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0564)
  have freshnessCertificate0566 : m ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0563 freshnessCertificate0565))
  have freshnessCertificate0567 : m ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0566)
  have freshnessCertificate0568 : n ∉ ({ a, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show n ≠ a from (by exact fresh_n_ne_a)),
          (show n ≠ m from (by exact fresh_n_ne_m))⟩)
  have freshnessCertificate0569 : n ∉ ((Wff.objMem a m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0568)
  have freshnessCertificate0570 : n ∉ ({ b, m } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show n ≠ b from (by exact fresh_n_ne_b)),
          (show n ≠ m from (by exact fresh_n_ne_m))⟩)
  have freshnessCertificate0571 : n ∉ ((Wff.objMem b m)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0570)
  have freshnessCertificate0572 : n ∉ (((Wff.objMem a m)).fv) ∪ (((Wff.objMem b m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0569 freshnessCertificate0571))
  have freshnessCertificate0573 : n ∉ ((syn_wa (.objMem a m) (.objMem b m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0572)
  have p0147 :=
    @g_cbvrexv (syn_wa (.objMem a n) (.objMem b n)) (syn_wa (.objMem a m) (.objMem b m)) n
      m (syn_cnnc) (by exact freshnessCertificate0029) (by exact freshnessCertificate0159)
      (by exact freshnessCertificate0567) (by exact freshnessCertificate0573) p0146
  have p0148 :=
    @g_n_3imtr4g
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
        (syn_wa (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018))
      syntaxFormula0025 (syn_wrex m (syn_cnnc) (syn_wa (.objMem a m) (.objMem b m)))
      syntaxFormula0006 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))) p0132
      p0143 p0147
  have p0149 :=
    @g_expr
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
      (syn_wa (.objMem c k) (.objMem d k)) syntaxFormula0018
      (.imp syntaxFormula0006 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      p0148
  have freshnessCertificate0574 : x ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0575 : x ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0574 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0576 : x ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show x ≠ a from (by exact fresh_x_ne_a)),
          (show x ≠ n from (by exact fresh_x_ne_n))⟩)
  have freshnessCertificate0577 : x ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0576)
  have freshnessCertificate0578 : x ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show x ≠ b from (by exact fresh_x_ne_b)),
          (show x ≠ n from (by exact fresh_x_ne_n))⟩)
  have freshnessCertificate0579 : x ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0578)
  have freshnessCertificate0580 : x ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0577 freshnessCertificate0579))
  have freshnessCertificate0581 : x ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0580)
  have freshnessCertificate0582 :
    x ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0581 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0583 :
    x ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0575 freshnessCertificate0582))
  have freshnessCertificate0584 :
    x ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0583)
  have freshnessCertificate0585 : y ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0586 : y ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0585 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0587 : y ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show y ≠ a from (by exact fresh_y_ne_a)),
          (show y ≠ n from (by exact fresh_y_ne_n))⟩)
  have freshnessCertificate0588 : y ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0587)
  have freshnessCertificate0589 : y ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show y ≠ b from (by exact fresh_y_ne_b)),
          (show y ≠ n from (by exact fresh_y_ne_n))⟩)
  have freshnessCertificate0590 : y ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0589)
  have freshnessCertificate0591 : y ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0588 freshnessCertificate0590))
  have freshnessCertificate0592 : y ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0591)
  have freshnessCertificate0593 :
    y ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0592 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0594 :
    y ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0586 freshnessCertificate0593))
  have freshnessCertificate0595 :
    y ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0594)
  have freshnessCertificate0596 : x ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ k from (by exact fresh_x_ne_k)))))
  have freshnessCertificate0597 : x ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0596 freshnessCertificate0574))
  have freshnessCertificate0598 : x ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0597)
  have freshnessCertificate0599 : x ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0100 freshnessCertificate0596))
  have freshnessCertificate0600 : x ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0599)
  have freshnessCertificate0601 : x ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0090 freshnessCertificate0596))
  have freshnessCertificate0602 : x ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0601)
  have freshnessCertificate0603 :
    x ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0600 freshnessCertificate0602))
  have freshnessCertificate0604 : x ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0603)
  have freshnessCertificate0605 :
    x ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0604 freshnessCertificate0584))
  have freshnessCertificate0606 :
    x ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0605)
  have freshnessCertificate0607 :
    x ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0606 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0608 :
    x ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0607)
  have freshnessCertificate0609 :
    x ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0608 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0610 :
    x ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0609)
  have freshnessCertificate0611 :
    x ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((Wff.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0598 freshnessCertificate0610))
  have freshnessCertificate0612 :
    x ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0611)
  have freshnessCertificate0613 : x ∉ ({ c, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show x ≠ c from (by exact fresh_x_ne_c)),
          (show x ≠ k from (by exact fresh_x_ne_k))⟩)
  have freshnessCertificate0614 : x ∉ ((Wff.objMem c k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0613)
  have freshnessCertificate0615 : x ∉ ({ d, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show x ≠ d from (by exact fresh_x_ne_d)),
          (show x ≠ k from (by exact fresh_x_ne_k))⟩)
  have freshnessCertificate0616 : x ∉ ((Wff.objMem d k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0615)
  have freshnessCertificate0617 : x ∉ (((Wff.objMem c k)).fv) ∪ (((Wff.objMem d k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0614 freshnessCertificate0616))
  have freshnessCertificate0618 : x ∉ ((syn_wa (.objMem c k) (.objMem d k))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0617)
  have freshnessCertificate0619 :
    x ∉
      (((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv) ∪
        (((syn_wa (.objMem c k) (.objMem d k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0612 freshnessCertificate0618))
  have freshnessCertificate0620 :
    x ∉
      ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa (.objMem c k) (.objMem d k)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0619)
  have freshnessCertificate0621 : y ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ k from (by exact fresh_y_ne_k)))))
  have freshnessCertificate0622 : y ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0621 freshnessCertificate0585))
  have freshnessCertificate0623 : y ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0622)
  have freshnessCertificate0624 : y ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0082 freshnessCertificate0621))
  have freshnessCertificate0625 : y ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0624)
  have freshnessCertificate0626 : y ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0104 freshnessCertificate0621))
  have freshnessCertificate0627 : y ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0626)
  have freshnessCertificate0628 :
    y ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0625 freshnessCertificate0627))
  have freshnessCertificate0629 : y ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0628)
  have freshnessCertificate0630 :
    y ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0629 freshnessCertificate0595))
  have freshnessCertificate0631 :
    y ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0630)
  have freshnessCertificate0632 :
    y ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0631 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0633 :
    y ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0632)
  have freshnessCertificate0634 :
    y ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0633 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0635 :
    y ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0634)
  have freshnessCertificate0636 :
    y ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((Wff.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0623 freshnessCertificate0635))
  have freshnessCertificate0637 :
    y ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0636)
  have freshnessCertificate0638 : y ∉ ({ c, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show y ≠ c from (by exact fresh_y_ne_c)),
          (show y ≠ k from (by exact fresh_y_ne_k))⟩)
  have freshnessCertificate0639 : y ∉ ((Wff.objMem c k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0638)
  have freshnessCertificate0640 : y ∉ ({ d, k } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show y ≠ d from (by exact fresh_y_ne_d)),
          (show y ≠ k from (by exact fresh_y_ne_k))⟩)
  have freshnessCertificate0641 : y ∉ ((Wff.objMem d k)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0640)
  have freshnessCertificate0642 : y ∉ (((Wff.objMem c k)).fv) ∪ (((Wff.objMem d k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0639 freshnessCertificate0641))
  have freshnessCertificate0643 : y ∉ ((syn_wa (.objMem c k) (.objMem d k))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0642)
  have freshnessCertificate0644 :
    y ∉
      (((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv) ∪
        (((syn_wa (.objMem c k) (.objMem d k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0637 freshnessCertificate0643))
  have freshnessCertificate0645 :
    y ∉
      ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa (.objMem c k) (.objMem d k)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0644)
  have p0150 :=
    @g_rexlimdvv
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
        (syn_wa (.objMem c k) (.objMem d k)))
      syntaxFormula0006 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))) x y
      (syn_ccompl (.cv c)) (syn_ccompl (.cv d)) (by exact freshnessCertificate0078)
      (by exact freshnessCertificate0584) (by exact freshnessCertificate0595)
      (by exact freshnessCertificate0620) (by exact freshnessCertificate0645)
      (show x ≠ y from (by exact fresh_x_ne_y)) p0149
  have p0151_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b
                (.imp syntaxFormula0002
                  (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
          (syn_wa (.classMem (.cv c) (.cv k)) (.classMem (.cv d) (.cv k))))
        (.imp syntaxFormula0008
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_wrex, syn_wex, syn_ccompl, syn_cnin, syn_wnan]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0150
  have freshnessCertificate0646 : c ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0647 : c ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0646 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0648 : c ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show c ≠ a from (by exact fresh_c_ne_a)),
          (show c ≠ n from (by exact fresh_c_ne_n))⟩)
  have freshnessCertificate0649 : c ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0648)
  have freshnessCertificate0650 : c ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show c ≠ b from (by exact fresh_c_ne_b)),
          (show c ≠ n from (by exact fresh_c_ne_n))⟩)
  have freshnessCertificate0651 : c ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0650)
  have freshnessCertificate0652 : c ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0649 freshnessCertificate0651)
  have freshnessCertificate0653 : c ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0652)
  have freshnessCertificate0654 :
    c ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0653 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0655 :
    c ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0647 freshnessCertificate0654)
  have freshnessCertificate0656 :
    c ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0655)
  have freshnessCertificate0657 : d ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show d ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0658 : d ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0657 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0659 : d ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show d ≠ a from (by exact fresh_d_ne_a)),
          (show d ≠ n from (by exact fresh_d_ne_n))⟩)
  have freshnessCertificate0660 : d ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0659)
  have freshnessCertificate0661 : d ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show d ≠ b from (by exact fresh_d_ne_b)),
          (show d ≠ n from (by exact fresh_d_ne_n))⟩)
  have freshnessCertificate0662 : d ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0661)
  have freshnessCertificate0663 : d ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0660 freshnessCertificate0662)
  have freshnessCertificate0664 : d ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0663)
  have freshnessCertificate0665 :
    d ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0664 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0666 :
    d ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0658 freshnessCertificate0665)
  have freshnessCertificate0667 :
    d ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0666)
  have freshnessCertificate0668 : c ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0048 freshnessCertificate0646)
  have freshnessCertificate0669 : c ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0668)
  have freshnessCertificate0670 : c ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0098 freshnessCertificate0048)
  have freshnessCertificate0671 : c ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0670)
  have freshnessCertificate0672 : c ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0067 freshnessCertificate0048)
  have freshnessCertificate0673 : c ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0672)
  have freshnessCertificate0674 :
    c ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0671 freshnessCertificate0673)
  have freshnessCertificate0675 : c ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0674)
  have freshnessCertificate0676 :
    c ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0675 freshnessCertificate0656)
  have freshnessCertificate0677 :
    c ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0676)
  have freshnessCertificate0678 :
    c ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0677 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0679 :
    c ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0678)
  have freshnessCertificate0680 :
    c ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0679 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0681 :
    c ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0680)
  have freshnessCertificate0682 :
    c ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((Wff.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0669 freshnessCertificate0681)
  have freshnessCertificate0683 :
    c ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0682)
  have freshnessCertificate0684 : d ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0047 freshnessCertificate0657)
  have freshnessCertificate0685 : d ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0684)
  have freshnessCertificate0686 : d ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0053 freshnessCertificate0047)
  have freshnessCertificate0687 : d ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0686)
  have freshnessCertificate0688 : d ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0102 freshnessCertificate0047)
  have freshnessCertificate0689 : d ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0688)
  have freshnessCertificate0690 :
    d ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0687 freshnessCertificate0689)
  have freshnessCertificate0691 : d ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0690)
  have freshnessCertificate0692 :
    d ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0691 freshnessCertificate0667)
  have freshnessCertificate0693 :
    d ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0692)
  have freshnessCertificate0694 :
    d ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0693 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0695 :
    d ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0694)
  have freshnessCertificate0696 :
    d ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0695 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0697 :
    d ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0696)
  have freshnessCertificate0698 :
    d ∉
      (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪
        (((Wff.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv) :=
    (fun hmem =>
      (Finset.mem_union.mp hmem).elim freshnessCertificate0685 freshnessCertificate0697)
  have freshnessCertificate0699 :
    d ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0698)
  have p0151 :=
    @g_rexlimdvva
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
      syntaxFormula0008 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))) c d
      (.cv k) (.cv k) (by exact freshnessCertificate0047)
      (by exact freshnessCertificate0656) (by exact freshnessCertificate0667)
      (by exact freshnessCertificate0683) (by exact freshnessCertificate0699)
      (show c ≠ d from (by exact fresh_c_ne_d)) p0151_e00_recanon
  have p0152 :=
    @g_syl5bi syntaxFormula0003 syntaxFormula0011
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))) p0053 p0151
  have p0153 :=
    @g_alrimi
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
      (.imp syntaxFormula0003 (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      b p0046 p0152
  have p0154 :=
    @g_alrimi
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))))
      (.all b (.imp syntaxFormula0003
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))
      a p0043 p0153
  have p0155 :=
    @g_ex (.classMem (.cv k) (syn_cnnc))
      (.all a (.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      (.all a (.all b (.imp syntaxFormula0003
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      p0154
  have freshnessCertificate0700 : m ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0223)
  have freshnessCertificate0701 : m ∉ ((Class.cv k)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show m ∉ ({ k } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show m ≠ k from (by exact fresh_m_ne_k)))))
  have freshnessCertificate0702 : m ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0700 freshnessCertificate0701))
  have freshnessCertificate0703 : m ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0702)
  have freshnessCertificate0704 : m ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0235)
  have freshnessCertificate0705 : m ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv k)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0704 freshnessCertificate0701))
  have freshnessCertificate0706 : m ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0705)
  have freshnessCertificate0707 :
    m ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv k))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv k))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0703 freshnessCertificate0706))
  have freshnessCertificate0708 : m ∉ (syntaxFormula0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0707)
  have freshnessCertificate0709 : m ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0159 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0710 :
    m ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0567 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0711 :
    m ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0709 freshnessCertificate0710))
  have freshnessCertificate0712 :
    m ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0711)
  have freshnessCertificate0713 :
    m ∉
      ((syntaxFormula0002).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0708 freshnessCertificate0712))
  have freshnessCertificate0714 :
    m ∉
      ((Wff.imp syntaxFormula0002
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0713)
  have freshnessCertificate0715 :
    m ∉
      (((Wff.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0714 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0716 :
    m ∉
      ((Wff.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0715)
  have freshnessCertificate0717 :
    m ∉
      (((Wff.all b (.imp syntaxFormula0002
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0716 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0718 :
    m ∉
      ((Wff.all a (.all b (.imp syntaxFormula0002
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0717)
  have freshnessCertificate0719 : k ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show k ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show k ≠ a from (by exact fresh_k_ne_a)))))
  have freshnessCertificate0720 : k ∉ ((syn_cpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0719)
  have freshnessCertificate0721 : k ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show k ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show k ≠ m from (by exact fresh_k_ne_m)))))
  have freshnessCertificate0722 : k ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0720 freshnessCertificate0721))
  have freshnessCertificate0723 : k ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv m))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0722)
  have freshnessCertificate0724 : k ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show k ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show k ≠ b from (by exact fresh_k_ne_b)))))
  have freshnessCertificate0725 : k ∉ ((syn_cpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0724)
  have freshnessCertificate0726 : k ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0725 freshnessCertificate0721))
  have freshnessCertificate0727 : k ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv m))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0726)
  have freshnessCertificate0728 :
    k ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (.cv m))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0723 freshnessCertificate0727))
  have freshnessCertificate0729 : k ∉ (syntaxFormula0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0728)
  have freshnessCertificate0730 : k ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0731 : k ∉ (((syn_cnnc)).fv).erase n :=
    (fun hmem => freshnessCertificate0730 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0732 : k ∉ ({ a, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show k ≠ a from (by exact fresh_k_ne_a)),
          (show k ≠ n from (by exact fresh_k_ne_n))⟩)
  have freshnessCertificate0733 : k ∉ ((Wff.objMem a n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0732)
  have freshnessCertificate0734 : k ∉ ({ b, n } : Finset Var) :=
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
      exact
        ⟨(show k ≠ b from (by exact fresh_k_ne_b)),
          (show k ≠ n from (by exact fresh_k_ne_n))⟩)
  have freshnessCertificate0735 : k ∉ ((Wff.objMem b n)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact freshnessCertificate0734)
  have freshnessCertificate0736 : k ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.objMem b n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0733 freshnessCertificate0735))
  have freshnessCertificate0737 : k ∉ ((syn_wa (.objMem a n) (.objMem b n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0736)
  have freshnessCertificate0738 :
    k ∉ (((syn_wa (.objMem a n) (.objMem b n))).fv).erase n :=
    (fun hmem => freshnessCertificate0737 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0739 :
    k ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.objMem a n) (.objMem b n))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0731 freshnessCertificate0738))
  have freshnessCertificate0740 :
    k ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0739)
  have freshnessCertificate0741 :
    k ∉
      ((syntaxFormula0000).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0729 freshnessCertificate0740))
  have freshnessCertificate0742 :
    k ∉
      ((Wff.imp syntaxFormula0000
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0741)
  have freshnessCertificate0743 :
    k ∉
      (((Wff.imp syntaxFormula0000
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0742 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0744 :
    k ∉
      ((Wff.all b (.imp syntaxFormula0000
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0743)
  have freshnessCertificate0745 :
    k ∉
      (((Wff.all b (.imp syntaxFormula0000
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0744 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0746 :
    k ∉
      ((Wff.all a (.all b (.imp syntaxFormula0000
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0745)
  have freshnessCertificate0747 : m ∉ ((syn_c0c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0748 : m ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_c0c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0700 freshnessCertificate0747))
  have freshnessCertificate0749 : m ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_c0c))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0748)
  have freshnessCertificate0750 : m ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((syn_c0c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0704 freshnessCertificate0747))
  have freshnessCertificate0751 : m ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (syn_c0c))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0750)
  have freshnessCertificate0752 :
    m ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (syn_c0c))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (syn_c0c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0749 freshnessCertificate0751))
  have freshnessCertificate0753 : m ∉ (syntaxFormula0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0752)
  have freshnessCertificate0754 :
    m ∉
      ((syntaxFormula0001).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0753 freshnessCertificate0712))
  have freshnessCertificate0755 :
    m ∉
      ((Wff.imp syntaxFormula0001
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0754)
  have freshnessCertificate0756 :
    m ∉
      (((Wff.imp syntaxFormula0001
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0755 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0757 :
    m ∉
      ((Wff.all b (.imp syntaxFormula0001
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0756)
  have freshnessCertificate0758 :
    m ∉
      (((Wff.all b (.imp syntaxFormula0001
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0757 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0759 :
    m ∉
      ((Wff.all a (.all b (.imp syntaxFormula0001
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0758)
  have freshnessCertificate0760 : m ∉ (((syn_cpw1 (.cv a))).fv) ∪ ((M).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0700
        (show m ∉ (M).fv from (by exact fresh_m_not_M)))
  have freshnessCertificate0761 : m ∉ ((Wff.classMem (syn_cpw1 (.cv a)) M)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0760)
  have freshnessCertificate0762 : m ∉ (((syn_cpw1 (.cv b))).fv) ∪ ((M).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0704
        (show m ∉ (M).fv from (by exact fresh_m_not_M)))
  have freshnessCertificate0763 : m ∉ ((Wff.classMem (syn_cpw1 (.cv b)) M)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0762)
  have freshnessCertificate0764 :
    m ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) M)).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) M)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0761 freshnessCertificate0763))
  have freshnessCertificate0765 :
    m ∉ ((syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0764)
  have freshnessCertificate0766 :
    m ∉
      (((syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0765 freshnessCertificate0712))
  have freshnessCertificate0767 :
    m ∉
      ((Wff.imp (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0766)
  have freshnessCertificate0768 :
    m ∉
      (((Wff.imp (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0767 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0769 :
    m ∉
      ((Wff.all b
          (.imp (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0768)
  have freshnessCertificate0770 :
    m ∉
      (((Wff.all b (.imp
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0769 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0771 :
    m ∉
      ((Wff.all a (.all b (.imp
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0770)
  have freshnessCertificate0772 : m ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0701 freshnessCertificate0156))
  have freshnessCertificate0773 : m ∉ ((syn_cplc (.cv k) (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0772)
  have freshnessCertificate0774 :
    m ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0700 freshnessCertificate0773))
  have freshnessCertificate0775 :
    m ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv k) (syn_c1c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0774)
  have freshnessCertificate0776 :
    m ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0704 freshnessCertificate0773))
  have freshnessCertificate0777 :
    m ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (syn_cplc (.cv k) (syn_c1c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0776)
  have freshnessCertificate0778 :
    m ∉
      (((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv k) (syn_c1c)))).fv) ∪
        (((Wff.classMem (syn_cpw1 (.cv b)) (syn_cplc (.cv k) (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0775 freshnessCertificate0777))
  have freshnessCertificate0779 : m ∉ (syntaxFormula0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0778)
  have freshnessCertificate0780 :
    m ∉
      ((syntaxFormula0003).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0779 freshnessCertificate0712))
  have freshnessCertificate0781 :
    m ∉
      ((Wff.imp syntaxFormula0003
          (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0780)
  have freshnessCertificate0782 :
    m ∉
      (((Wff.imp syntaxFormula0003
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))).fv).erase
        b :=
    (fun hmem => freshnessCertificate0781 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0783 :
    m ∉
      ((Wff.all b (.imp syntaxFormula0003
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0782)
  have freshnessCertificate0784 :
    m ∉
      (((Wff.all b (.imp syntaxFormula0003
                (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))).fv).erase
        a :=
    (fun hmem => freshnessCertificate0783 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0785 :
    m ∉
      ((Wff.all a (.all b (.imp syntaxFormula0003
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact freshnessCertificate0784)
  have p0156 :=
    @g_finds
      (.all a (.all b (.imp syntaxFormula0000
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      (.all a (.all b (.imp syntaxFormula0001
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      (.all a (.all b (.imp syntaxFormula0002
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      (.all a (.all b (.imp syntaxFormula0003
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      (.all a (.all b
          (.imp (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      m k M (by exact (show m ∉ (M).fv from (by exact fresh_m_not_M)))
      (by exact freshnessCertificate0718) (by exact freshnessCertificate0746)
      (by exact freshnessCertificate0759) (by exact freshnessCertificate0771)
      (by exact freshnessCertificate0785) (show m ≠ k from (by exact fresh_m_ne_k)) p0000
      p0005 p0010 p0015 p0020 p0040 p0155
  have p0157 := @g_elex (syn_cpw1 A) M
  have p0158 := @g_pw1exb A
  have p0159 :=
    @g_sylib (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 A) (syn_cvv))
      (.classMem A (syn_cvv)) p0157 p0158
  have p0160 := @g_elex (syn_cpw1 B) M
  have p0161 := @g_pw1exb B
  have p0162 :=
    @g_sylib (.classMem (syn_cpw1 B) M) (.classMem (syn_cpw1 B) (syn_cvv))
      (.classMem B (syn_cvv)) p0160 p0161
  have p0163 := @g_pw1eq (.cv a) A
  have p0164 := @g_eleq1d (.classEq (.cv a) A) (syn_cpw1 (.cv a)) (syn_cpw1 A) M p0163
  have p0165 := @g_pw1eq (.cv b) B
  have p0166 := @g_eleq1d (.classEq (.cv b) B) (syn_cpw1 (.cv b)) (syn_cpw1 B) M p0165
  have p0167 :=
    @g_bi2anan9 (.classEq (.cv a) A) (.classMem (syn_cpw1 (.cv a)) M)
      (.classMem (syn_cpw1 A) M) (.classEq (.cv b) B) (.classMem (syn_cpw1 (.cv b)) M)
      (.classMem (syn_cpw1 B) M) p0164 p0166
  have p0168 := @g_eleq1 (.cv a) A (.cv n)
  have p0169 := @g_eleq1 (.cv b) B (.cv n)
  have p0170_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) A) (syn_wb (.objMem a n) (.classMem A (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb]
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
      p0168
  have p0170_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) B) (syn_wb (.objMem b n) (.classMem B (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb]
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
      p0169
  have p0170 :=
    @g_bi2anan9 (.classEq (.cv a) A) (.objMem a n) (.classMem A (.cv n))
      (.classEq (.cv b) B) (.objMem b n) (.classMem B (.cv n)) p0170_e00_recanon
      p0170_e01_recanon
  have freshnessCertificate0786 : n ∉ (((Class.cv a)).fv) ∪ ((A).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0033
        (show n ∉ (A).fv from (by exact dv_A_n)))
  have freshnessCertificate0787 : n ∉ ((Wff.classEq (.cv a) A)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0786)
  have freshnessCertificate0788 : n ∉ (((Class.cv b)).fv) ∪ ((B).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0036
        (show n ∉ (B).fv from (by exact dv_B_n)))
  have freshnessCertificate0789 : n ∉ ((Wff.classEq (.cv b) B)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0788)
  have freshnessCertificate0790 :
    n ∉ (((Wff.classEq (.cv a) A)).fv) ∪ (((Wff.classEq (.cv b) B)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0787 freshnessCertificate0789))
  have freshnessCertificate0791 :
    n ∉ ((syn_wa (.classEq (.cv a) A) (.classEq (.cv b) B))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0790)
  have p0171 :=
    @g_rexbidv (syn_wa (.classEq (.cv a) A) (.classEq (.cv b) B))
      (syn_wa (.objMem a n) (.objMem b n))
      (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n))) n (syn_cnnc)
      (by exact freshnessCertificate0791) p0170
  have p0172 :=
    @g_imbi12d (syn_wa (.classEq (.cv a) A) (.classEq (.cv b) B))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
      (syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))) p0167
      p0171
  have freshnessCertificate0792 : a ∉ ((syn_cpw1 A)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
  have freshnessCertificate0793 : a ∉ (((syn_cpw1 A)).fv) ∪ ((M).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0792
        (show a ∉ (M).fv from (by exact fresh_a_not_M)))
  have freshnessCertificate0794 : a ∉ ((Wff.classMem (syn_cpw1 A) M)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0793)
  have freshnessCertificate0795 : a ∉ ((syn_cpw1 B)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact (show a ∉ (B).fv from (by exact fresh_a_not_B)))
  have freshnessCertificate0796 : a ∉ (((syn_cpw1 B)).fv) ∪ ((M).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0795
        (show a ∉ (M).fv from (by exact fresh_a_not_M)))
  have freshnessCertificate0797 : a ∉ ((Wff.classMem (syn_cpw1 B) M)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0796)
  have freshnessCertificate0798 :
    a ∉ (((Wff.classMem (syn_cpw1 A) M)).fv) ∪ (((Wff.classMem (syn_cpw1 B) M)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0794 freshnessCertificate0797))
  have freshnessCertificate0799 :
    a ∉ ((syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0798)
  have freshnessCertificate0800 : a ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ n from (by exact fresh_a_ne_n)))))
  have freshnessCertificate0801 : a ∉ ((A).fv) ∪ (((Class.cv n)).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A))
        freshnessCertificate0800)
  have freshnessCertificate0802 : a ∉ ((Wff.classMem A (.cv n))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0801)
  have freshnessCertificate0803 : a ∉ ((B).fv) ∪ (((Class.cv n)).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (B).fv from (by exact fresh_a_not_B))
        freshnessCertificate0800)
  have freshnessCertificate0804 : a ∉ ((Wff.classMem B (.cv n))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0803)
  have freshnessCertificate0805 :
    a ∉ (((Wff.classMem A (.cv n))).fv) ∪ (((Wff.classMem B (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0802 freshnessCertificate0804))
  have freshnessCertificate0806 :
    a ∉ ((syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0805)
  have freshnessCertificate0807 :
    a ∉ (((syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))).fv).erase n :=
    (fun hmem => freshnessCertificate0806 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0808 :
    a ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0123 freshnessCertificate0807))
  have freshnessCertificate0809 :
    a ∉
      ((syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0808)
  have freshnessCertificate0810 :
    a ∉
      (((syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0799 freshnessCertificate0809))
  have freshnessCertificate0811 :
    a ∉
      ((Wff.imp (syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))
          (syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0810)
  have freshnessCertificate0812 : b ∉ ((syn_cpw1 A)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
  have freshnessCertificate0813 : b ∉ (((syn_cpw1 A)).fv) ∪ ((M).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0812
        (show b ∉ (M).fv from (by exact fresh_b_not_M)))
  have freshnessCertificate0814 : b ∉ ((Wff.classMem (syn_cpw1 A) M)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0813)
  have freshnessCertificate0815 : b ∉ ((syn_cpw1 B)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
  have freshnessCertificate0816 : b ∉ (((syn_cpw1 B)).fv) ∪ ((M).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim freshnessCertificate0815
        (show b ∉ (M).fv from (by exact fresh_b_not_M)))
  have freshnessCertificate0817 : b ∉ ((Wff.classMem (syn_cpw1 B) M)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0816)
  have freshnessCertificate0818 :
    b ∉ (((Wff.classMem (syn_cpw1 A) M)).fv) ∪ (((Wff.classMem (syn_cpw1 B) M)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0814 freshnessCertificate0817))
  have freshnessCertificate0819 :
    b ∉ ((syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0818)
  have freshnessCertificate0820 : b ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ n from (by exact fresh_b_ne_n)))))
  have freshnessCertificate0821 : b ∉ ((A).fv) ∪ (((Class.cv n)).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (A).fv from (by exact fresh_b_not_A))
        freshnessCertificate0820)
  have freshnessCertificate0822 : b ∉ ((Wff.classMem A (.cv n))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0821)
  have freshnessCertificate0823 : b ∉ ((B).fv) ∪ (((Class.cv n)).fv) :=
    (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (B).fv from (by exact fresh_b_not_B))
        freshnessCertificate0820)
  have freshnessCertificate0824 : b ∉ ((Wff.classMem B (.cv n))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0823)
  have freshnessCertificate0825 :
    b ∉ (((Wff.classMem A (.cv n))).fv) ∪ (((Wff.classMem B (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0822 freshnessCertificate0824))
  have freshnessCertificate0826 :
    b ∉ ((syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa];
      exact freshnessCertificate0825)
  have freshnessCertificate0827 :
    b ∉ (((syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))).fv).erase n :=
    (fun hmem => freshnessCertificate0826 (Finset.mem_of_mem_erase hmem))
  have freshnessCertificate0828 :
    b ∉
      ((((syn_cnnc)).fv).erase n) ∪
        ((((syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))).fv).erase n) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0143 freshnessCertificate0827))
  have freshnessCertificate0829 :
    b ∉
      ((syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex];
      exact freshnessCertificate0828)
  have freshnessCertificate0830 :
    b ∉
      (((syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))).fv) ∪
        (((syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0819 freshnessCertificate0829))
  have freshnessCertificate0831 :
    b ∉
      ((Wff.imp (syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))
          (syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact freshnessCertificate0830)
  have p0173 :=
    @g_spc2gv
      (.imp (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
        (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))
      syntaxFormula0026 a b A B (syn_cvv) (syn_cvv)
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show a ∉ (B).fv from (by exact fresh_a_not_B)))
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (by exact freshnessCertificate0811) (by exact freshnessCertificate0831)
      (show a ≠ b from (by exact fresh_a_ne_b)) p0172
  have p0174 :=
    @g_syl2an (.classMem (syn_cpw1 A) M) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.imp (.all a (.all b (.imp
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
              (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n)))))) syntaxFormula0026)
      (.classMem (syn_cpw1 B) M) p0159 p0162 p0173
  have p0175 :=
    @g_pm2_43b
      (.all a (.all b
          (.imp (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      (syn_wa (.classMem (syn_cpw1 A) M) (.classMem (syn_cpw1 B) M))
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))) p0174
  have p0176 :=
    @g_syl (.classMem M (syn_cnnc))
      (.all a (.all b
          (.imp (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv b)) M))
            (syn_wrex n (syn_cnnc) (syn_wa (.objMem a n) (.objMem b n))))))
      syntaxFormula0026 p0156 p0175
  have p0177 :=
    @g_n_3impib (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 A) M)
      (.classMem (syn_cpw1 B) M)
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem A (.cv n)) (.classMem B (.cv n)))) p0176
  exact p0177


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart052`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nnpw1ex (n : Var) (M : Class) (a : Var) (dv_M_a : a ∉ M.fv)
    (dv_M_n : n ∉ M.fv) (dv_a_n : a ≠ n) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) :=
  by
  let proofSupport : Finset Var := ({ n } : Finset Var) ∪ M.fv ∪ ({ a } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_n : p ≠ n := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_p : n ≠ p := Ne.symm fresh_p_ne_n
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_a : p ≠ a := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_p : a ≠ p := Ne.symm fresh_p_ne_a
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_a : b ≠ a := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_b : a ≠ b := Ne.symm fresh_b_ne_a
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_ne_n : q ≠ n := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_a : q ≠ a := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_b : p ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_p : b ≠ p := Ne.symm fresh_p_ne_b
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have fresh_b_ne_q : b ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_b : q ≠ b := Ne.symm fresh_b_ne_q
  have freeVariableCertificate0 : n ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      (Ne.symm dv_a_n), not_false_eq_true]
  have p0000 :=
    @g_ncfinraise (.cv a) (.cv a) n M freeVariableCertificate0 freeVariableCertificate0
  have p0001 := @g_anidm (.classMem (syn_cpw1 (.cv a)) (.cv n))
  have p0002 :=
    @g_rexbii
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (.cv n)))
      (.classMem (syn_cpw1 (.cv a)) (.cv n)) n (syn_cnnc) p0001
  have p0003 :=
    @g_sylib
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem (.cv a) M) (.classMem (.cv a) M))
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
          (.classMem (syn_cpw1 (.cv a)) (.cv n))))
      (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0000 p0002
  have p0004 :=
    @g_n_3anidm23 (.classMem M (syn_cnnc)) (.classMem (.cv a) M)
      (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0003
  have p0005 :=
    @g_ex (.classMem M (syn_cnnc)) (.classMem (.cv a) M)
      (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0004
  have p0006 :=
    @g_ancld (.classMem M (syn_cnnc)) (.classMem (.cv a) M)
      (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0005
  have freeVariableCertificate1 : a ∉ ((Wff.classMem M (syn_cnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, dv_M_a, or_false, not_false_eq_true]
  have p0007 :=
    @g_eximdv (.classMem M (syn_cnnc)) (.classMem (.cv a) M)
      (syn_wa (.classMem (.cv a) M)
        (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))))
      a freeVariableCertificate1 p0006
  have p0008 :=
    @g_imp (.classMem M (syn_cnnc)) (syn_wex a (.classMem (.cv a) M))
      (syn_wex a (syn_wa (.classMem (.cv a) M)
          (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
      p0007
  have p0009 := @g_n0 a M (by exact (show a ∉ (M).fv from (by exact dv_M_a)))
  have p0010 :=
    @g_anbi2i (syn_wne M (syn_c0)) (syn_wex a (.classMem (.cv a) M))
      (.classMem M (syn_cnnc)) p0009
  have p0011 :=
    @g_rexcom (.classMem (syn_cpw1 (.cv a)) (.cv n)) n a (syn_cnnc) M
      (by
        exact
          (show a ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show n ∉ (M).fv from (by exact dv_M_n)))
      (show n ≠ a from (by exact Ne.symm dv_a_n))
  have p0012 :=
    (Nominal.biimpRefl
      (syn_wrex a M (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
  have p0013 :=
    @g_bitri (syn_wrex n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))
      (syn_wrex a M (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))))
      (syn_wex a (syn_wa (.classMem (.cv a) M)
          (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
      p0011 p0012
  have p0014 :=
    @g_n_3imtr4i (syn_wa (.classMem M (syn_cnnc)) (syn_wex a (.classMem (.cv a) M)))
      (syn_wex a (syn_wa (.classMem (.cv a) M)
          (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
      (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_wrex n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) p0008
      p0010 p0013
  have p0015 := @g_pw1eq (.cv a) (.cv b)
  have p0016_e00_recanon :
    Nominal.NPrf (.imp (.objEq a b) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss
          syn_c1c syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @g_eleq1d (.objEq a b) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv p) p0016_e00_recanon
  have freeVariableCertificate2 : b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv p))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_b_ne_a, fresh_b_ne_p, or_false, not_false_eq_true]
  have freeVariableCertificate3 : a ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv p))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_a_ne_b, fresh_a_ne_p, or_false, not_false_eq_true]
  have p0017 :=
    @g_cbvrexv (.classMem (syn_cpw1 (.cv a)) (.cv p))
      (.classMem (syn_cpw1 (.cv b)) (.cv p)) a b M
      (by exact (show a ∉ (M).fv from (by exact dv_M_a)))
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) freeVariableCertificate2
      freeVariableCertificate3 p0016
  have p0018 :=
    @g_anbi2i (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))
      (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (.cv p)))
      (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0017
  have freeVariableCertificate4 : b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_b_ne_a, fresh_b_ne_n, or_false, not_false_eq_true]
  have p0019 :=
    @g_reeanv (.classMem (syn_cpw1 (.cv a)) (.cv n))
      (.classMem (syn_cpw1 (.cv b)) (.cv p)) a b M M
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (by exact (show a ∉ (M).fv from (by exact dv_M_a))) freeVariableCertificate4
      freeVariableCertificate3 (show a ≠ b from (by exact fresh_a_ne_b))
  have p0020 :=
    @g_bitr4i
      (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))
        (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p))))
      (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))
        (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (.cv p))))
      (syn_wrex a M (syn_wrex b M (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))))
      p0018 p0019
  have p0021 :=
    @g_simplll (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
  have p0022 :=
    @g_simprll
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (.classMem (.cv a) M) (.classMem (.cv b) M)
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))
  have p0023 :=
    @g_simprlr
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (.classMem (.cv a) M) (.classMem (.cv b) M)
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))
  have freeVariableCertificate5 : q ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_q_ne_a, not_false_eq_true]
  have freeVariableCertificate6 : q ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_q_ne_b, not_false_eq_true]
  have p0024 :=
    @g_ncfinraise (.cv a) (.cv b) q M freeVariableCertificate5 freeVariableCertificate6
  have p0025 :=
    @g_syl3anc
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))))
      (.classMem M (syn_cnnc)) (.classMem (.cv a) M) (.classMem (.cv b) M)
      (syn_wrex q (syn_cnnc) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
          (.classMem (syn_cpw1 (.cv b)) (.cv q))))
      p0021 p0022 p0023 p0024
  have p0026 :=
    @g_simp1rl (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))
      (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
      (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
          (.classMem (syn_cpw1 (.cv b)) (.cv q))))
  have p0027 :=
    @g_simp3l
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
      (.classMem (.cv q) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)))
  have p0028 :=
    @g_simp2rl (.classMem (syn_cpw1 (.cv a)) (.cv n))
      (.classMem (syn_cpw1 (.cv b)) (.cv p))
      (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
          (.classMem (syn_cpw1 (.cv b)) (.cv q))))
  have p0029 :=
    @g_simp3rl (.classMem (syn_cpw1 (.cv a)) (.cv q))
      (.classMem (syn_cpw1 (.cv b)) (.cv q)) (.classMem (.cv q) (syn_cnnc))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
  have p0030 := @g_nnceleq (syn_cpw1 (.cv a)) (.cv n) (.cv q)
  have p0031_e04_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv a)) (.cv q)))) (.objEq n q)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0030
  have p0031 :=
    @g_syl22anc
      (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
            (.classMem (syn_cpw1 (.cv b)) (.cv q)))))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (.cv q))
      (.objEq n q) p0026 p0027 p0028 p0029 p0031_e04_recanon
  have p0032 :=
    @g_simp1rr (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))
      (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
      (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
          (.classMem (syn_cpw1 (.cv b)) (.cv q))))
  have p0033 :=
    @g_simp2rr (.classMem (syn_cpw1 (.cv a)) (.cv n))
      (.classMem (syn_cpw1 (.cv b)) (.cv p))
      (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
          (.classMem (syn_cpw1 (.cv b)) (.cv q))))
  have p0034 :=
    @g_simp3rr (.classMem (syn_cpw1 (.cv a)) (.cv q))
      (.classMem (syn_cpw1 (.cv b)) (.cv q)) (.classMem (.cv q) (syn_cnnc))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
  have p0035 := @g_nnceleq (syn_cpw1 (.cv b)) (.cv p) (.cv q)
  have p0036_e04_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv p) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) (.cv p))
            (.classMem (syn_cpw1 (.cv b)) (.cv q)))) (.objEq p q)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0035
  have p0036 :=
    @g_syl22anc
      (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
            (.classMem (syn_cpw1 (.cv b)) (.cv q)))))
      (.classMem (.cv p) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv b)) (.cv p)) (.classMem (syn_cpw1 (.cv b)) (.cv q))
      (.objEq p q) p0032 p0027 p0033 p0034 p0036_e04_recanon
  have p0037_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
            (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
          (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
            (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
              (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc))
            (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
              (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.classEq (.cv n) (.cv q))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0031
  have p0037_e01_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
            (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
          (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
            (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
              (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc))
            (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
              (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.classEq (.cv p) (.cv q))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0036
  have p0037 :=
    @g_eqtr4d
      (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
            (.classMem (syn_cpw1 (.cv b)) (.cv q)))))
      (.cv n) (.cv q) (.cv p) p0037_e00_recanon p0037_e01_recanon
  have p0038_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
            (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
          (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
            (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
              (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc))
            (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
              (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.objEq n p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0037
  have p0038 :=
    @g_n_3expa
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
      (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
          (.classMem (syn_cpw1 (.cv b)) (.cv q))))
      (.objEq n p) p0038_e00_recanon
  have p0039 :=
    @g_exp32
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))))
      (.classMem (.cv q) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)))
      (.objEq n p) p0038
  have freeVariableCertificate7 : q ∉ ((Wff.objEq n p)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_q_ne_n, fresh_q_ne_p, or_false, not_false_eq_true]
  have freeVariableCertificate8 :
    q ∉
      ((syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
            (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
          (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
            (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
              (.classMem (syn_cpw1 (.cv b)) (.cv p)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_q_not_M, fresh_q_ne_n,
      fresh_q_ne_p, fresh_q_ne_a, fresh_q_ne_b, or_false, not_false_eq_true]
  have p0040 :=
    @g_rexlimdv
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)))
      (.objEq n p) q (syn_cnnc) freeVariableCertificate7 freeVariableCertificate8 p0039
  have p0041 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))))
      (syn_wrex q (syn_cnnc) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q))
          (.classMem (syn_cpw1 (.cv b)) (.cv q))))
      (.objEq n p) p0025 p0040
  have p0042 :=
    @g_exp32
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))
      (.objEq n p) p0041
  have freeVariableCertificate9 : a ∉ ((Wff.objEq n p)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, dv_a_n, fresh_a_ne_p, or_false, not_false_eq_true]
  have freeVariableCertificate10 : b ∉ ((Wff.objEq n p)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_n, fresh_b_ne_p, or_false, not_false_eq_true]
  have freeVariableCertificate11 :
    a ∉
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, dv_M_a, dv_a_n, fresh_a_ne_p, or_false, not_false_eq_true]
  have freeVariableCertificate12 :
    b ∉
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
          (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_b_not_M, fresh_b_ne_n, fresh_b_ne_p, or_false,
      not_false_eq_true]
  have p0043 :=
    @g_rexlimdvv
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))
      (.objEq n p) a b M M (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      freeVariableCertificate9 freeVariableCertificate10 freeVariableCertificate11
      freeVariableCertificate12 (show a ≠ b from (by exact fresh_a_ne_b)) p0042
  have p0044 :=
    @g_syl5bi
      (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))
        (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p))))
      (syn_wrex a M (syn_wrex b M (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv p)))))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))
      (.objEq n p) p0020 p0043
  have freeVariableCertificate13 :
    n ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, dv_M_n, or_false, not_false_eq_true]
  have freeVariableCertificate14 :
    p ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_p_not_M, or_false, not_false_eq_true]
  have p0045 :=
    @g_ralrimivva (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (.imp (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))
          (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))) (.objEq n p))
      n p (syn_cnnc) (syn_cnnc)
      (by
        exact
          (show p ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate13 freeVariableCertificate14
      (show n ≠ p from (by exact fresh_n_ne_p)) p0044
  have p0046 := @g_eleq2 (.cv n) (.cv p) (syn_cpw1 (.cv a))
  have p0047_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n p) (syn_wb (.classMem (syn_cpw1 (.cv a)) (.cv n))
          (.classMem (syn_cpw1 (.cv a)) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss
          syn_c1c syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0046
  have p0047 :=
    @g_rexbidv (.objEq n p) (.classMem (syn_cpw1 (.cv a)) (.cv n))
      (.classMem (syn_cpw1 (.cv a)) (.cv p)) a M freeVariableCertificate9
      p0047_e00_recanon
  have freeVariableCertificate15 :
    p ∉ ((syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_p_not_M, fresh_p_ne_a, fresh_p_ne_n, or_false,
      and_false, not_false_eq_true]
  have freeVariableCertificate16 :
    n ∉ ((syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, dv_M_n, fresh_n_ne_p, (Ne.symm dv_a_n), or_false, and_false,
      not_false_eq_true]
  have p0048 :=
    @g_reu4 (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))
      (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p))) n p (syn_cnnc)
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show p ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate15 freeVariableCertificate16
      (show n ≠ p from (by exact fresh_n_ne_p)) p0047
  have p0049 :=
    @g_sylanbrc (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_wrex n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))
      (syn_wral n (syn_cnnc) (syn_wral p (syn_cnnc) (.imp
            (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))
              (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))) (.objEq n p))))
      (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) p0014
      p0045 p0048
  exact p0049

@[expose]
noncomputable def g_tfinex (A : Class) :
    Nominal.NPrf (.classMem (syn_ctfin A) (syn_cvv)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin x A y
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0001 := @g_n_0ex
  have p0002 :=
    @g_iotaex
      (syn_wa (.classMem (.cv x) (syn_cnnc))
        (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x))))
      x
  have p0003 :=
    @g_ifex (.classEq A (syn_c0)) (syn_c0)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc))
          (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x)))))
      p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_ctfin A)
      (syn_cif (.classEq A (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc))
            (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x))))))
      (syn_cvv) p0000 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end
