/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part017

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part018`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sfinltfin`. -/
@[expose]
noncomputable def gSfinltfin (P : Class) (Q : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWsfin M N) (synWsfin P Q))
          (.classMem (synCopk M P) (synCltfin))) (.classMem (synCopk N Q) (synCltfin))) :=
  by
  let proofSupport : Finset Var := P.fv ∪ Q.fv ∪ M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let s : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let g : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  let x : Var := freshVar proofSupport 7
  let u : Var := freshVar proofSupport 8
  let n : Var := freshVar proofSupport 9
  let m : Var := freshVar proofSupport 10
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_P : a ∉ P.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_Q : a ∉ Q.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_P : b ∉ P.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_Q : b ∉ Q.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_P : r ∉ P.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_r_not_Q : r ∉ Q.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_M : r ∉ M.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_N : r ∉ N.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_s_not_P : s ∉ P.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_s_not_Q : s ∉ Q.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_not_M : s ∉ M.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_not_N : s ∉ N.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_P : t ∉ P.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_t_not_Q : t ∉ Q.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_M : t ∉ M.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_N : t ∉ N.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_g_not_P : g ∉ P.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_g_not_Q : g ∉ Q.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_M : g ∉ M.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_N : g ∉ N.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_not_P : d ∉ P.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_Q : d ∉ Q.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_M : d ∉ M.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_N : d ∉ N.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_x_not_P : x ∉ P.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_Q : x ∉ Q.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_u_not_P : u ∉ P.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_Q : u ∉ Q.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_M : u ∉ M.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_N : u ∉ N.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 9 ∉ proofSupport
    exact freshVar_not_mem proofSupport 9
  have fresh_n_not_P : n ∉ P.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_Q : n ∉ Q.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have fresh_a_ne_s : a ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_s_ne_a : s ≠ a := Ne.symm fresh_a_ne_s
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_a_ne_g : a ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_g_ne_a : g ≠ a := Ne.symm fresh_a_ne_g
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_u : a ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
  have fresh_a_ne_n : a ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_b_ne_r : b ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_b : r ≠ b := Ne.symm fresh_b_ne_r
  have fresh_b_ne_s : b ≠ s :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_s_ne_b : s ≠ b := Ne.symm fresh_b_ne_s
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have fresh_b_ne_g : b ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_g_ne_b : g ≠ b := Ne.symm fresh_b_ne_g
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_u : b ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_u_ne_b : u ≠ b := Ne.symm fresh_b_ne_u
  have fresh_b_ne_n : b ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
  have fresh_n_ne_b : n ≠ b := Ne.symm fresh_b_ne_n
  have fresh_r_ne_s : r ≠ s :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_s_ne_r : s ≠ r := Ne.symm fresh_r_ne_s
  have fresh_r_ne_t : r ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_r : t ≠ r := Ne.symm fresh_r_ne_t
  have fresh_r_ne_g : r ≠ g :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_g_ne_r : g ≠ r := Ne.symm fresh_r_ne_g
  have fresh_r_ne_d : r ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_d_ne_r : d ≠ r := Ne.symm fresh_r_ne_d
  have fresh_r_ne_x : r ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_u : r ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_u_ne_r : u ≠ r := Ne.symm fresh_r_ne_u
  have fresh_r_ne_n : r ≠ n :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
  have fresh_n_ne_r : n ≠ r := Ne.symm fresh_r_ne_n
  have fresh_s_ne_t : s ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_s : t ≠ s := Ne.symm fresh_s_ne_t
  have fresh_s_ne_g : s ≠ g :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_g_ne_s : g ≠ s := Ne.symm fresh_s_ne_g
  have fresh_s_ne_d : s ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have fresh_s_ne_x : s ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_x_ne_s : x ≠ s := Ne.symm fresh_s_ne_x
  have fresh_s_ne_u : s ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_u_ne_s : u ≠ s := Ne.symm fresh_s_ne_u
  have fresh_s_ne_n : s ≠ n :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_n_ne_s : n ≠ s := Ne.symm fresh_s_ne_n
  have fresh_t_ne_g : t ≠ g :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_g_ne_t : g ≠ t := Ne.symm fresh_t_ne_g
  have fresh_t_ne_d : t ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_t : d ≠ t := Ne.symm fresh_t_ne_d
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_u_ne_t : u ≠ t := Ne.symm fresh_t_ne_u
  have fresh_t_ne_n : t ≠ n :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 4) (j := 9) (by decide)
  have fresh_n_ne_t : n ≠ t := Ne.symm fresh_t_ne_n
  have fresh_g_ne_d : g ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_g_ne_x : g ≠ x :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_x_ne_g : x ≠ g := Ne.symm fresh_g_ne_x
  have fresh_g_ne_u : g ≠ u :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_u_ne_g : u ≠ g := Ne.symm fresh_g_ne_u
  have fresh_g_ne_n : g ≠ n :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
  have fresh_n_ne_g : n ≠ g := Ne.symm fresh_g_ne_n
  have fresh_d_ne_x : d ≠ x :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_d_ne_u : d ≠ u :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_u_ne_d : u ≠ d := Ne.symm fresh_d_ne_u
  have fresh_d_ne_n : d ≠ n :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_n_ne_d : n ≠ d := Ne.symm fresh_d_ne_n
  have fresh_u_ne_n : u ≠ n :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_n_ne_u : n ≠ u := Ne.symm fresh_u_ne_n
  have fresh_u_ne_m : u ≠ m :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 8) (j := 10) (by decide)
  have fresh_m_ne_u : m ≠ u := Ne.symm fresh_u_ne_m
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have dv_cache_0001 : a ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_M, not_false_eq_true])
  have dv_cache_0002 : a ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_N, not_false_eq_true])
  have dv_cache_0003 : b ∉ (P).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_P, not_false_eq_true])
  have dv_cache_0004 : b ∉ (Q).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_Q, not_false_eq_true])
  have dv_cache_0005 :
    b ∉ ((synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_a, fresh_b_not_M, fresh_b_not_N, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    a ∉ ((synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_b, fresh_a_not_P, fresh_a_not_Q, or_false,
          not_false_eq_true])
  have dv_cache_0007 : r ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_a, not_false_eq_true])
  have dv_cache_0008 : s ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_b, not_false_eq_true])
  have dv_cache_0009 : s ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : s ∉ ((synWa (.objMem a r) (.objMem a r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_s_ne_a, fresh_s_ne_r, or_false, not_false_eq_true])
  have dv_cache_0012 : r ∉ ((synWa (.objMem b s) (.objMem b s))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_r_ne_b, fresh_r_ne_s, or_false, not_false_eq_true])
  have dv_cache_0013 : r ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ s from (by exact fresh_r_ne_s))
  have dv_cache_0014 : a ∉ ((Class.cv r)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_r, not_false_eq_true])
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
  have dv_cache_0016 : t ∉ ((Class.cv r)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_r, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((Class.cv s)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_s, not_false_eq_true])
  have dv_cache_0018 : g ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_b, not_false_eq_true])
  have dv_cache_0019 : d ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_b, not_false_eq_true])
  have dv_cache_0020 : g ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_r, not_false_eq_true])
  have dv_cache_0021 : d ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_r, not_false_eq_true])
  have dv_cache_0022 : g ∉ ((synCplc (.cv t) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_t, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0023 : d ∉ ((synCplc (.cv t) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_t, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0024 : g ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show g ≠ d from (by exact fresh_g_ne_d))
  have dv_cache_0025 : x ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_d, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((Class.cv g)).fv :=
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
          fresh_x_ne_g, not_false_eq_true])
  have dv_cache_0027 : u ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_a, not_false_eq_true])
  have dv_cache_0028 : u ∉ ((Class.cv g)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_g, not_false_eq_true])
  have dv_cache_0029 : u ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_r, not_false_eq_true])
  have dv_cache_0030 : n ∉ ((synCdif (synCpw (.cv b)) (synCpw (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_b, fresh_n_ne_g, or_false, not_false_eq_true])
  have dv_cache_0031 : m ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_m_ne_n, not_false_eq_true])
  have dv_cache_0032 : m ∉ ((Class.cv u)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_m_ne_u, not_false_eq_true])
  have dv_cache_0033 : m ∉ ((synCplc (.cv u) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_u, fresh_m_ne_n, or_false, not_false_eq_true])
  have dv_cache_0034 : n ∉ ((Wff.classMem (synCopk (.cv u) Q) (synCltfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_u, fresh_n_not_Q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0035 :
    n ∉
      ((synWa (synWa (synW3a
              (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
                (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                  (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                  (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
              (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
                (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
                (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))) (synWa
              (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
              (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
                (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
          (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
              (.classMem (synCpw (.cv g)) (.cv u)))
            (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wpss, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_t, fresh_n_ne_s,
          fresh_n_ne_r, fresh_n_ne_a, fresh_n_not_M, fresh_n_not_N, fresh_n_ne_b,
          fresh_n_not_P, fresh_n_not_Q, fresh_n_ne_g, fresh_n_ne_d, fresh_n_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0036 :
    u ∉
      ((Wff.imp (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
          (.classMem (synCopk N Q) (synCltfin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wpss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_g, fresh_u_ne_b, fresh_u_not_N, fresh_u_not_Q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0037 :
    u ∉
      ((synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))).fv :=
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
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_t, fresh_u_ne_s,
          fresh_u_ne_r, fresh_u_ne_a, fresh_u_not_M, fresh_u_not_N, fresh_u_ne_b,
          fresh_u_not_P, fresh_u_not_Q, fresh_u_ne_g, fresh_u_ne_d,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0038 : x ∉ ((Wff.classMem (synCopk N Q) (synCltfin))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_x_not_N, fresh_x_not_Q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0039 :
    x ∉
      ((synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_s,
          fresh_x_ne_r, fresh_x_ne_a, fresh_x_not_M, fresh_x_not_N, fresh_x_ne_b,
          fresh_x_not_P, fresh_x_not_Q, fresh_x_ne_g, fresh_x_ne_d,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0040 : g ∉ ((Wff.classMem (synCopk N Q) (synCltfin))).fv :=
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
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_g_not_N, fresh_g_not_Q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0041 : d ∉ ((Wff.classMem (synCopk N Q) (synCltfin))).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_d_not_N, fresh_d_not_Q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0042 :
    g ∉
      ((synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))).fv :=
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
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_t, fresh_g_ne_s,
          fresh_g_ne_r, fresh_g_ne_a, fresh_g_not_M, fresh_g_not_N, fresh_g_ne_b,
          fresh_g_not_P, fresh_g_not_Q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0043 :
    d ∉
      ((synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))).fv :=
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
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_t, fresh_d_ne_s,
          fresh_d_ne_r, fresh_d_ne_a, fresh_d_not_M, fresh_d_not_N, fresh_d_ne_b,
          fresh_d_not_P, fresh_d_not_Q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0044 : t ∉ ((Wff.classMem (synCopk N Q) (synCltfin))).fv :=
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
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_t_not_N, fresh_t_not_Q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0045 :
    t ∉
      ((synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))))).fv :=
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
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_not_M, fresh_t_not_N, fresh_t_ne_b,
          fresh_t_not_P, fresh_t_not_Q, fresh_t_ne_r, fresh_t_ne_s,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0046 :
    r ∉
      ((Wff.imp (.classMem (synCopk M P) (synCltfin))
          (.classMem (synCopk N Q) (synCltfin)))).fv :=
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
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_r_not_M, fresh_r_not_P, fresh_r_not_N, fresh_r_not_Q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0047 :
    s ∉
      ((Wff.imp (.classMem (synCopk M P) (synCltfin))
          (.classMem (synCopk N Q) (synCltfin)))).fv :=
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
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_s_not_M, fresh_s_not_P, fresh_s_not_N, fresh_s_not_Q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0048 :
    r ∉
      ((synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))).fv :=
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
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_a, fresh_r_not_M, fresh_r_not_N, fresh_r_ne_b,
          fresh_r_not_P, fresh_r_not_Q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0049 :
    s ∉
      ((synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))).fv :=
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
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_a, fresh_s_not_M, fresh_s_not_N, fresh_s_ne_b,
          fresh_s_not_P, fresh_s_not_Q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0050 :
    a ∉
      ((Wff.imp (.classMem (synCopk M P) (synCltfin))
          (.classMem (synCopk N Q) (synCltfin)))).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_a_not_M, fresh_a_not_P, fresh_a_not_N, fresh_a_not_Q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0051 :
    b ∉
      ((Wff.imp (.classMem (synCopk M P) (synCltfin))
          (.classMem (synCopk N Q) (synCltfin)))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_b_not_M, fresh_b_not_P, fresh_b_not_N, fresh_b_not_Q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0052 :
    a ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_a_not_M, fresh_a_not_P, fresh_a_not_N, fresh_a_not_Q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0053 :
    b ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_b_not_M, fresh_b_not_P, fresh_b_not_N, fresh_b_not_Q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin M N a
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin P Q b
      dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gN3an6 (.classMem M (synCnnc)) (.classMem P (synCnnc)) (.classMem N (synCnnc))
      (.classMem Q (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N)))
      (synWex b (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
  have p0003 :=
    @gEeanv (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
      (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)) a b
      dv_cache_0005 dv_cache_0006
  have p0004 :=
    @gSimp1l (.classMem M (synCnnc)) (.classMem P (synCnnc))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
        (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
  have p0005 :=
    @gSimp3ll (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N)
      (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))
      (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
  have p0006 := @gNcfinlower (.cv a) (.cv a) r M dv_cache_0007 dv_cache_0007
  have p0007_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem (synCpw1 (.cv a)) M)
          (.classMem (synCpw1 (.cv a)) M))
        (synWrex r (synCnnc) (synWa (.objMem a r) (.objMem a r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synCpw1 synCin synCcompl synCnin
          synWnan synCpw synWss synC1c synWex synCsn synWrex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0006
  have p0007 :=
    @gSyl3anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.classMem M (synCnnc)) (.classMem (synCpw1 (.cv a)) M)
      (.classMem (synCpw1 (.cv a)) M)
      (synWrex r (synCnnc) (synWa (.objMem a r) (.objMem a r))) p0004 p0005 p0005
      p0007_e03_recanon
  have p0008 :=
    @gSimp1r (.classMem M (synCnnc)) (.classMem P (synCnnc))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
        (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
  have p0009 :=
    @gSimp3rl (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)
      (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
      (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
  have p0010 := @gNcfinlower (.cv b) (.cv b) s P dv_cache_0008 dv_cache_0008
  have p0011_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem P (synCnnc)) (.classMem (synCpw1 (.cv b)) P)
          (.classMem (synCpw1 (.cv b)) P))
        (synWrex s (synCnnc) (synWa (.objMem b s) (.objMem b s)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synCpw1 synCin synCcompl synCnin
          synWnan synCpw synWss synC1c synWex synCsn synWrex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0010
  have p0011 :=
    @gSyl3anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.classMem P (synCnnc)) (.classMem (synCpw1 (.cv b)) P)
      (.classMem (synCpw1 (.cv b)) P)
      (synWrex s (synCnnc) (synWa (.objMem b s) (.objMem b s))) p0008 p0009 p0009
      p0011_e03_recanon
  have p0012 :=
    @gReeanv (synWa (.objMem a r) (.objMem a r)) (synWa (.objMem b s) (.objMem b s)) r
      s (synCnnc) (synCnnc) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0013 := @gSimpl (.objMem a r) (.objMem a r)
  have p0014 := @gSimpl (.objMem b s) (.objMem b s)
  have p0015 :=
    @gAnim12i (synWa (.objMem a r) (.objMem a r)) (.objMem a r)
      (synWa (.objMem b s) (.objMem b s)) (.objMem b s) p0013 p0014
  have p0016 :=
    @gAdantr
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.classMem (synCpw1 (.cv a)) M)
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
      p0005
  have p0017 :=
    @gSimprll
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc))
      (synWa (.objMem a r) (.objMem b s))
  have p0018 :=
    @gSimprrl
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc))) (.objMem a r)
      (.objMem b s)
  have p0019 := @gTfinpw1 (.cv a) (.cv r)
  have p0020_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv r) (synCnnc)) (.objMem a r))
        (.classMem (synCpw1 (.cv a)) (synCtfin (.cv r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCnnc synCint synCpw1 synCin synCcompl synCnin synWnan
          synCpw synWss synC1c synWex synCsn synCtfin synCif synWo synC0 synCdif
          synCvv synCio synCuni
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @gSyl2anc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (.cv r) (synCnnc)) (.objMem a r)
      (.classMem (synCpw1 (.cv a)) (synCtfin (.cv r))) p0017 p0018 p0020_e02_recanon
  have p0021 := @gElin (synCpw1 (.cv a)) M (synCtfin (.cv r))
  have p0022 :=
    @gSylanbrc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw1 (.cv a)) (synCtfin (.cv r)))
      (.classMem (synCpw1 (.cv a)) (synCin M (synCtfin (.cv r)))) p0016 p0020 p0021
  have p0023 := @gN0i (synCin M (synCtfin (.cv r))) (synCpw1 (.cv a))
  have p0024 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (synCpw1 (.cv a)) (synCin M (synCtfin (.cv r))))
      (.neg (.classEq (synCin M (synCtfin (.cv r))) (synC0))) p0022 p0023
  have p0025 :=
    @gSimpl1l (.classMem M (synCnnc)) (.classMem P (synCnnc))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
        (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
  have p0026 := @gNe0i (.cv r) (.cv a)
  have p0027_e01_recanon : Nominal.NPrf (.imp (.objMem a r) (synWne (.cv r) (synC0))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.objMem a r) (synWne (.cv r) (synC0)) p0018 p0027_e01_recanon
  have p0028 := @gTfinprop (.cv r) a dv_cache_0014
  have p0029 :=
    @gSimpld (synWa (.classMem (.cv r) (synCnnc)) (synWne (.cv r) (synC0)))
      (.classMem (synCtfin (.cv r)) (synCnnc))
      (synWrex a (.cv r) (.classMem (synCpw1 (.cv a)) (synCtfin (.cv r)))) p0028
  have p0030 :=
    @gSyl2anc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (.cv r) (synCnnc)) (synWne (.cv r) (synC0))
      (.classMem (synCtfin (.cv r)) (synCnnc)) p0017 p0027 p0029
  have p0031 := @gNndisjeq M (synCtfin (.cv r))
  have p0032 :=
    @gSyl2anc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem M (synCnnc)) (.classMem (synCtfin (.cv r)) (synCnnc))
      (synWo (.classEq (synCin M (synCtfin (.cv r))) (synC0))
        (.classEq M (synCtfin (.cv r))))
      p0025 p0030 p0031
  have p0033 :=
    @gOrel1 (.classEq (synCin M (synCtfin (.cv r))) (synC0))
      (.classEq M (synCtfin (.cv r)))
  have p0034 :=
    @gSylc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.neg (.classEq (synCin M (synCtfin (.cv r))) (synC0)))
      (synWo (.classEq (synCin M (synCtfin (.cv r))) (synC0))
        (.classEq M (synCtfin (.cv r))))
      (.classEq M (synCtfin (.cv r))) p0024 p0032 p0033
  have p0035 :=
    @gAdantr
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.classMem (synCpw1 (.cv b)) P)
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
      p0009
  have p0036 :=
    @gSimprlr
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc))
      (synWa (.objMem a r) (.objMem b s))
  have p0037 :=
    @gSimprrr
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc))) (.objMem a r)
      (.objMem b s)
  have p0038 := @gTfinpw1 (.cv b) (.cv s)
  have p0039_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv s) (synCnnc)) (.objMem b s))
        (.classMem (synCpw1 (.cv b)) (synCtfin (.cv s)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCnnc synCint synCpw1 synCin synCcompl synCnin synWnan
          synCpw synWss synC1c synWex synCsn synCtfin synCif synWo synC0 synCdif
          synCvv synCio synCuni
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @gSyl2anc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (.cv s) (synCnnc)) (.objMem b s)
      (.classMem (synCpw1 (.cv b)) (synCtfin (.cv s))) p0036 p0037 p0039_e02_recanon
  have p0040 := @gElin (synCpw1 (.cv b)) P (synCtfin (.cv s))
  have p0041 :=
    @gSylanbrc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw1 (.cv b)) (synCtfin (.cv s)))
      (.classMem (synCpw1 (.cv b)) (synCin P (synCtfin (.cv s)))) p0035 p0039 p0040
  have p0042 := @gN0i (synCin P (synCtfin (.cv s))) (synCpw1 (.cv b))
  have p0043 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (synCpw1 (.cv b)) (synCin P (synCtfin (.cv s))))
      (.neg (.classEq (synCin P (synCtfin (.cv s))) (synC0))) p0041 p0042
  have p0044 :=
    @gSimpl1r (.classMem M (synCnnc)) (.classMem P (synCnnc))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
        (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
  have p0045 := @gNe0i (.cv s) (.cv b)
  have p0046_e01_recanon : Nominal.NPrf (.imp (.objMem b s) (synWne (.cv s) (synC0))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0045
  have p0046 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.objMem b s) (synWne (.cv s) (synC0)) p0037 p0046_e01_recanon
  have p0047 := @gTfinprop (.cv s) a dv_cache_0015
  have p0048 :=
    @gSimpld (synWa (.classMem (.cv s) (synCnnc)) (synWne (.cv s) (synC0)))
      (.classMem (synCtfin (.cv s)) (synCnnc))
      (synWrex a (.cv s) (.classMem (synCpw1 (.cv a)) (synCtfin (.cv s)))) p0047
  have p0049 :=
    @gSyl2anc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (.cv s) (synCnnc)) (synWne (.cv s) (synC0))
      (.classMem (synCtfin (.cv s)) (synCnnc)) p0036 p0046 p0048
  have p0050 := @gNndisjeq P (synCtfin (.cv s))
  have p0051 :=
    @gSyl2anc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem P (synCnnc)) (.classMem (synCtfin (.cv s)) (synCnnc))
      (synWo (.classEq (synCin P (synCtfin (.cv s))) (synC0))
        (.classEq P (synCtfin (.cv s))))
      p0044 p0049 p0050
  have p0052 :=
    @gOrel1 (.classEq (synCin P (synCtfin (.cv s))) (synC0))
      (.classEq P (synCtfin (.cv s)))
  have p0053 :=
    @gSylc
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.neg (.classEq (synCin P (synCtfin (.cv s))) (synC0)))
      (synWo (.classEq (synCin P (synCtfin (.cv s))) (synC0))
        (.classEq P (synCtfin (.cv s))))
      (.classEq P (synCtfin (.cv s))) p0043 p0051 p0052
  have p0054 := @gTfinltfin (.cv r) (.cv s)
  have p0055 :=
    @gAd2antrl (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
      (synWb (.classMem (synCopk (.cv r) (.cv s)) (synCltfin))
        (.classMem (synCopk (synCtfin (.cv r)) (synCtfin (.cv s))) (synCltfin)))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.objMem a r) (.objMem b s)) p0054
  have p0056 :=
    @gOpkltfing t (.cv r) (.cv s) (synCnnc) (synCnnc) dv_cache_0016 dv_cache_0017
  have p0057 :=
    @gAd2antrl (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
      (synWb (.classMem (synCopk (.cv r) (.cv s)) (synCltfin))
        (synWa (synWne (.cv r) (synC0)) (synWrex t (synCnnc)
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.objMem a r) (.objMem b s)) p0056
  have p0058 :=
    @gSimp2rr (.objMem a r) (.objMem b s)
      (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.classMem (.cv t) (synCnnc))
        (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
  have p0059 :=
    @gSimp3r
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
      (.classMem (.cv t) (synCnnc))
      (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))
  have p0060_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (.classMem (.cv b) (.cv s))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _)
      p0058
  have p0060 :=
    @gEleqtrd
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.cv b) (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)) p0060_e00_recanon
      p0059
  have p0061 := @gAddcass (.cv r) (.cv t) (synC1c)
  have p0062 :=
    @gSyl6eleq
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.cv b) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))
      (synCplc (.cv r) (synCplc (.cv t) (synC1c))) p0060 p0061
  have p0063 :=
    @gEladdc (.cv b) (.cv r) (synCplc (.cv t) (synC1c)) g d dv_cache_0018 dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0064 := @gN0nelsuc (.cv t)
  have p0065 :=
    @gSimprlr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c)))
      (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
        (.classEq (.cv b) (synCun (.cv g) (.cv d))))
  have p0066 := @gEleq1 (.cv d) (synC0) (synCplc (.cv t) (synC1c))
  have p0067 :=
    @gSyl5ibcom
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (.cv d) (synCplc (.cv t) (synC1c))) (.classEq (.cv d) (synC0))
      (.classMem (synC0) (synCplc (.cv t) (synC1c))) p0065 p0066
  have p0068 :=
    @gMtoi
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classEq (.cv d) (synC0)) (.classMem (synC0) (synCplc (.cv t) (synC1c))) p0064
      p0067
  have p0069 := (Nominal.biimpRefl (synWne (.cv d) (synC0)))
  have p0070 :=
    @gSylibr
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.neg (.classEq (.cv d) (synC0))) (synWne (.cv d) (synC0)) p0068 p0069
  have p0071 := @gN0 x (.cv d) dv_cache_0025
  have p0072 := @gSsun2 (.cv d) (.cv g)
  have p0073 := @gSseq2 (.cv b) (synCun (.cv g) (.cv d)) (.cv d)
  have p0074 :=
    @gMpbiri (.classEq (.cv b) (synCun (.cv g) (.cv d))) (synWss (.cv d) (.cv b))
      (synWss (.cv d) (synCun (.cv g) (.cv d))) p0072 p0073
  have p0075 :=
    @gSseld (.classEq (.cv b) (synCun (.cv g) (.cv d))) (.cv d) (.cv b) (.cv x) p0074
  have p0076 := @gDisjr x (.cv g) (.cv d) dv_cache_0026 dv_cache_0025
  have p0077 := @gRsp (.neg (.objMem x g)) x (.cv d)
  have p0078_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCin (.cv g) (.cv d)) (synC0))
        (synWral x (.cv d) (.neg (.objMem x g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCin synCcompl synCnin synWnan synWa synC0 synCdif synCvv
          synWral
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0076
  have p0078_e01_recanon :
    Nominal.NPrf
      (.imp (synWral x (.cv d) (.neg (.objMem x g)))
        (.imp (.objMem x d) (.neg (.objMem x g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWral
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0078 :=
    @gSylbi (.classEq (synCin (.cv g) (.cv d)) (synC0))
      (synWral x (.cv d) (.neg (.objMem x g))) (.imp (.objMem x d) (.neg (.objMem x g)))
      p0078_e00_recanon p0078_e01_recanon
  have p0079_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (synCun (.cv g) (.cv d))) (.imp (.objMem x d) (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCun synCnin synWnan synWa synCcompl
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0075
  have p0079 :=
    @gAnim12ii (.classEq (.cv b) (synCun (.cv g) (.cv d))) (.objMem x d) (.objMem x b)
      (.classEq (synCin (.cv g) (.cv d)) (synC0)) (.neg (.objMem x g)) p0079_e00_recanon
      p0078
  have p0080 :=
    @gAncoms (.classEq (.cv b) (synCun (.cv g) (.cv d)))
      (.classEq (synCin (.cv g) (.cv d)) (synC0))
      (.imp (.objMem x d) (synWa (.objMem x b) (.neg (.objMem x g)))) p0079
  have p0081 :=
    @gAd2antll
      (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
        (.classEq (.cv b) (synCun (.cv g) (.cv d))))
      (.imp (.objMem x d) (synWa (.objMem x b) (.neg (.objMem x g))))
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c)))) p0080
  have p0082 := @gVex x
  have p0083 := @gSnelpw (.cv x) (.cv b) p0082
  have p0084 := @gSnelpw (.cv x) (.cv g) p0082
  have p0085_e00_recanon :
    Nominal.NPrf (synWb (.classMem (synCsn (.cv x)) (synCpw (.cv g))) (.objMem x g)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn synCpw synWss synCin synCcompl synCnin synWnan synWa
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
      p0084
  have p0085 :=
    @gNotbii (.classMem (synCsn (.cv x)) (synCpw (.cv g))) (.objMem x g)
      p0085_e00_recanon
  have p0086_e00_recanon :
    Nominal.NPrf (synWb (.classMem (synCsn (.cv x)) (synCpw (.cv b))) (.objMem x b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn synCpw synWss synCin synCcompl synCnin synWnan synWa
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
      p0083
  have p0086 :=
    @gAnbi12i (.classMem (synCsn (.cv x)) (synCpw (.cv b))) (.objMem x b)
      (.neg (.classMem (synCsn (.cv x)) (synCpw (.cv g)))) (.neg (.objMem x g))
      p0086_e00_recanon p0085
  have p0087 := @gSsun1 (.cv g) (.cv d)
  have p0088 := @gSseq2 (.cv b) (synCun (.cv g) (.cv d)) (.cv g)
  have p0089 :=
    @gMpbiri (.classEq (.cv b) (synCun (.cv g) (.cv d))) (synWss (.cv g) (.cv b))
      (synWss (.cv g) (synCun (.cv g) (.cv d))) p0087 p0088
  have p0090 := @gSspwb (.cv g) (.cv b)
  have p0091 :=
    @gSylib (.classEq (.cv b) (synCun (.cv g) (.cv d))) (synWss (.cv g) (.cv b))
      (synWss (synCpw (.cv g)) (synCpw (.cv b))) p0089 p0090
  have p0092 :=
    @gAdantl (.classEq (.cv b) (synCun (.cv g) (.cv d)))
      (synWss (synCpw (.cv g)) (synCpw (.cv b)))
      (.classEq (synCin (.cv g) (.cv d)) (synC0)) p0091
  have p0093 :=
    @gAd2antll
      (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
        (.classEq (.cv b) (synCun (.cv g) (.cv d))))
      (synWss (synCpw (.cv g)) (synCpw (.cv b)))
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c)))) p0092
  have p0094 := @gEleq2 (synCpw (.cv g)) (synCpw (.cv b)) (synCsn (.cv x))
  have p0095 :=
    @gBiimprcd (.classEq (synCpw (.cv g)) (synCpw (.cv b)))
      (.classMem (synCsn (.cv x)) (synCpw (.cv g)))
      (.classMem (synCsn (.cv x)) (synCpw (.cv b))) p0094
  have p0096 :=
    @gCon3d (.classMem (synCsn (.cv x)) (synCpw (.cv b)))
      (.classEq (synCpw (.cv g)) (synCpw (.cv b)))
      (.classMem (synCsn (.cv x)) (synCpw (.cv g))) p0095
  have p0097 :=
    @gImp (.classMem (synCsn (.cv x)) (synCpw (.cv b)))
      (.neg (.classMem (synCsn (.cv x)) (synCpw (.cv g))))
      (.neg (.classEq (synCpw (.cv g)) (synCpw (.cv b)))) p0096
  have p0098 :=
    @gAnim2i
      (synWa (.classMem (synCsn (.cv x)) (synCpw (.cv b)))
        (.neg (.classMem (synCsn (.cv x)) (synCpw (.cv g)))))
      (.neg (.classEq (synCpw (.cv g)) (synCpw (.cv b))))
      (synWss (synCpw (.cv g)) (synCpw (.cv b))) p0097
  have p0099 := @gDfpss2 (synCpw (.cv g)) (synCpw (.cv b))
  have p0100 :=
    @gSylibr
      (synWa (synWss (synCpw (.cv g)) (synCpw (.cv b)))
        (synWa (.classMem (synCsn (.cv x)) (synCpw (.cv b)))
          (.neg (.classMem (synCsn (.cv x)) (synCpw (.cv g))))))
      (synWa (synWss (synCpw (.cv g)) (synCpw (.cv b)))
        (.neg (.classEq (synCpw (.cv g)) (synCpw (.cv b)))))
      (synWpss (synCpw (.cv g)) (synCpw (.cv b))) p0098 p0099
  have p0101 :=
    @gSimp2ll (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc))
      (synWa (.objMem a r) (.objMem b s))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.classMem (.cv t) (synCnnc))
        (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
  have p0102 :=
    @gAdantr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem (.cv r) (synCnnc))
      (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
        (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
          (.classEq (.cv b) (synCun (.cv g) (.cv d)))))
      p0101
  have p0103 :=
    @gSimp2rl (.objMem a r) (.objMem b s)
      (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.classMem (.cv t) (synCnnc))
        (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
  have p0104 :=
    @gAdantr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.objMem a r)
      (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
        (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
          (.classEq (.cv b) (synCun (.cv g) (.cv d)))))
      p0103
  have p0105 :=
    @gSimprll
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c)))
      (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
        (.classEq (.cv b) (synCun (.cv g) (.cv d))))
  have p0106 :=
    @gNnpweq (.cv a) (.cv g) u (.cv r) dv_cache_0027 dv_cache_0028 dv_cache_0029
  have p0107_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv r) (synCnnc)) (.objMem a r) (.objMem g r))
        (synWrex u (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synWrex synWex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0106
  have p0107 :=
    @gSyl3anc
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (.cv r) (synCnnc)) (.objMem a r) (.objMem g r)
      (synWrex u (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))))
      p0102 p0104 p0105 p0107_e03_recanon
  have p0108 :=
    @gSimpr2l (.classMem (synCpw (.cv a)) (.cv u)) (.classMem (synCpw (.cv g)) (.cv u))
      (.classMem (.cv u) (synCnnc)) (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
  have p0109 :=
    @gSimp3lr (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N)
      (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))
      (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
  have p0110 :=
    @gN3ad2ant1
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
      (.classMem (synCpw (.cv a)) N)
      (synWa (.classMem (.cv t) (synCnnc))
        (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
      p0109
  have p0111 :=
    @gAd2antrr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem (synCpw (.cv a)) N)
      (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
        (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
          (.classEq (.cv b) (synCun (.cv g) (.cv d)))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      p0110
  have p0112 := @gElin (synCpw (.cv a)) (.cv u) N
  have p0113 :=
    @gSylanbrc
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (synCpw (.cv a)) (.cv u)) (.classMem (synCpw (.cv a)) N)
      (.classMem (synCpw (.cv a)) (synCin (.cv u) N)) p0108 p0111 p0112
  have p0114 := @gN0i (synCin (.cv u) N) (synCpw (.cv a))
  have p0115 :=
    @gSyl
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (synCpw (.cv a)) (synCin (.cv u) N))
      (.neg (.classEq (synCin (.cv u) N) (synC0))) p0113 p0114
  have p0116 :=
    @gSimpr1
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (.cv u) (synCnnc))
      (synWa (.classMem (synCpw (.cv a)) (.cv u)) (.classMem (synCpw (.cv g)) (.cv u)))
      (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
  have p0117 :=
    @gSimp12l (.classMem N (synCnnc)) (.classMem Q (synCnnc))
      (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
        (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
      (synWa (.classMem (.cv t) (synCnnc))
        (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
  have p0118 :=
    @gAd2antrr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem N (synCnnc))
      (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
        (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
          (.classEq (.cv b) (synCun (.cv g) (.cv d)))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      p0117
  have p0119 := @gNndisjeq (.cv u) N
  have p0120 :=
    @gSyl2anc
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (.cv u) (synCnnc)) (.classMem N (synCnnc))
      (synWo (.classEq (synCin (.cv u) N) (synC0)) (.classEq (.cv u) N)) p0116 p0118
      p0119
  have p0121 := @gOrel1 (.classEq (synCin (.cv u) N) (synC0)) (.classEq (.cv u) N)
  have p0122 :=
    @gSylc
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.neg (.classEq (synCin (.cv u) N) (synC0)))
      (synWo (.classEq (synCin (.cv u) N) (synC0)) (.classEq (.cv u) N))
      (.classEq (.cv u) N) p0115 p0120 p0121
  have p0123 :=
    @gSimp3rr (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)
      (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
      (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
  have p0124 :=
    @gN3ad2ant1
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
      (.classMem (synCpw (.cv b)) Q)
      (synWa (.classMem (.cv t) (synCnnc))
        (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
      p0123
  have p0125 :=
    @gAd2antrr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem (synCpw (.cv b)) Q)
      (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
        (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
          (.classEq (.cv b) (synCun (.cv g) (.cv d)))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      p0124
  have p0126 :=
    @gSimp12r (.classMem N (synCnnc)) (.classMem Q (synCnnc))
      (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
        (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
      (synWa (.classMem (.cv t) (synCnnc))
        (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
  have p0127 :=
    @gAd2antrr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem Q (synCnnc))
      (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
        (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
          (.classEq (.cv b) (synCun (.cv g) (.cv d)))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      p0126
  have p0128 := @gElunii (synCpw (.cv b)) Q (synCnnc)
  have p0129 :=
    @gSyl2anc
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (synCpw (.cv b)) Q) (.classMem Q (synCnnc))
      (.classMem (synCpw (.cv b)) (synCuni (synCnnc))) p0125 p0127 p0128
  have p0130 := (Nominal.classEqRefl (synCfin))
  have p0131 :=
    @gSyl6eleqr
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (synCpw (.cv b)) (synCuni (synCnnc)) (synCfin) p0129 p0130
  have p0132 := @gVex b
  have p0133 := @gPwex (.cv b) p0132
  have p0134 := @gVex g
  have p0135 := @gPwex (.cv g) p0134
  have p0136 := @gDifex (synCpw (.cv b)) (synCpw (.cv g)) p0133 p0135
  have p0137 := @gDifss (synCpw (.cv b)) (synCpw (.cv g))
  have p0138 :=
    @gSsfin (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCpw (.cv b)) (synCvv)
  have p0139 :=
    @gMp3an13 (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCvv))
      (.classMem (synCpw (.cv b)) (synCfin))
      (synWss (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCpw (.cv b)))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCfin)) p0136 p0137
      p0138
  have p0140 :=
    @gSyl
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (synCpw (.cv b)) (synCfin))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCfin)) p0131 p0139
  have p0141 := @gElfin n (synCdif (synCpw (.cv b)) (synCpw (.cv g))) dv_cache_0030
  have p0142 :=
    @gAdantr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem (synCpw (.cv b)) Q)
      (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
        (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
          (.classEq (.cv b) (synCun (.cv g) (.cv d)))))
      p0124
  have p0143 :=
    @gN3ad2ant1
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      (.classMem (synCpw (.cv b)) Q)
      (synWa (.classMem (.cv n) (synCnnc))
        (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n)))
      p0142
  have p0144 := @gUndif1 (synCpw (.cv b)) (synCpw (.cv g))
  have p0145 := @gUncom (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCpw (.cv g))
  have p0146 :=
    @gEqtr3i (synCun (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCpw (.cv g)))
      (synCun (synCpw (.cv b)) (synCpw (.cv g)))
      (synCun (synCpw (.cv g)) (synCdif (synCpw (.cv b)) (synCpw (.cv g)))) p0144
      p0145
  have p0147 :=
    @gSimp23
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (.cv u) (synCnnc))
      (synWa (.classMem (synCpw (.cv a)) (.cv u)) (.classMem (synCpw (.cv g)) (.cv u)))
      (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWa (.classMem (.cv n) (synCnnc))
        (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n)))
  have p0148 :=
    @gPssssd
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (synCpw (.cv g)) (synCpw (.cv b)) p0147
  have p0149 := @gSsequn2 (synCpw (.cv g)) (synCpw (.cv b))
  have p0150 :=
    @gSylib
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (synWss (synCpw (.cv g)) (synCpw (.cv b)))
      (.classEq (synCun (synCpw (.cv b)) (synCpw (.cv g))) (synCpw (.cv b))) p0148
      p0149
  have p0151 :=
    @gSyl5eqr
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (synCun (synCpw (.cv g)) (synCdif (synCpw (.cv b)) (synCpw (.cv g))))
      (synCun (synCpw (.cv b)) (synCpw (.cv g))) (synCpw (.cv b)) p0146 p0150
  have p0152 :=
    @gSimp22r (.classMem (synCpw (.cv a)) (.cv u)) (.classMem (synCpw (.cv g)) (.cv u))
      (.classMem (.cv u) (synCnnc)) (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synWa (.classMem (.cv n) (synCnnc))
        (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n)))
  have p0153 :=
    @gSimp3r
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      (.classMem (.cv n) (synCnnc))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
  have p0154 := @gDisjdif (synCpw (.cv g)) (synCpw (.cv b))
  have p0155 :=
    @gA1i
      (.classEq (synCin (synCpw (.cv g)) (synCdif (synCpw (.cv b)) (synCpw (.cv g))))
        (synC0))
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      p0154
  have p0156 :=
    @gEladdci (synCpw (.cv g)) (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv u)
      (.cv n)
  have p0157 :=
    @gSyl3anc
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem (synCpw (.cv g)) (.cv u))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
      (.classEq (synCin (synCpw (.cv g)) (synCdif (synCpw (.cv b)) (synCpw (.cv g))))
        (synC0))
      (.classMem (synCun (synCpw (.cv g)) (synCdif (synCpw (.cv b)) (synCpw (.cv g))))
        (synCplc (.cv u) (.cv n)))
      p0152 p0153 p0155 p0156
  have p0158 :=
    @gEqeltrrd
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (synCun (synCpw (.cv g)) (synCdif (synCpw (.cv b)) (synCpw (.cv g))))
      (synCpw (.cv b)) (synCplc (.cv u) (.cv n)) p0151 p0157
  have p0159 := @gElin (synCpw (.cv b)) Q (synCplc (.cv u) (.cv n))
  have p0160 :=
    @gSylanbrc
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem (synCpw (.cv b)) Q)
      (.classMem (synCpw (.cv b)) (synCplc (.cv u) (.cv n)))
      (.classMem (synCpw (.cv b)) (synCin Q (synCplc (.cv u) (.cv n)))) p0143 p0158
      p0159
  have p0161 := @gN0i (synCin Q (synCplc (.cv u) (.cv n))) (synCpw (.cv b))
  have p0162 :=
    @gSyl
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem (synCpw (.cv b)) (synCin Q (synCplc (.cv u) (.cv n))))
      (.neg (.classEq (synCin Q (synCplc (.cv u) (.cv n))) (synC0))) p0160 p0161
  have p0163 :=
    @gAdantr
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem Q (synCnnc))
      (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
        (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
          (.classEq (.cv b) (synCun (.cv g) (.cv d)))))
      p0126
  have p0164 :=
    @gN3ad2ant1
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      (.classMem Q (synCnnc))
      (synWa (.classMem (.cv n) (synCnnc))
        (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n)))
      p0163
  have p0165 :=
    @gSimp21
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (.cv u) (synCnnc))
      (synWa (.classMem (synCpw (.cv a)) (.cv u)) (.classMem (synCpw (.cv g)) (.cv u)))
      (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWa (.classMem (.cv n) (synCnnc))
        (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n)))
  have p0166 :=
    @gSimp3l
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      (.classMem (.cv n) (synCnnc))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
  have p0167 := @gNncaddccl (.cv u) (.cv n)
  have p0168 :=
    @gSyl2anc
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem (.cv u) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv u) (.cv n)) (synCnnc)) p0165 p0166 p0167
  have p0169 := @gNndisjeq Q (synCplc (.cv u) (.cv n))
  have p0170 :=
    @gSyl2anc
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem Q (synCnnc)) (.classMem (synCplc (.cv u) (.cv n)) (synCnnc))
      (synWo (.classEq (synCin Q (synCplc (.cv u) (.cv n))) (synC0))
        (.classEq Q (synCplc (.cv u) (.cv n))))
      p0164 p0168 p0169
  have p0171 :=
    @gOrel1 (.classEq (synCin Q (synCplc (.cv u) (.cv n))) (synC0))
      (.classEq Q (synCplc (.cv u) (.cv n)))
  have p0172 :=
    @gSylc
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.neg (.classEq (synCin Q (synCplc (.cv u) (.cv n))) (synC0)))
      (synWo (.classEq (synCin Q (synCplc (.cv u) (.cv n))) (synC0))
        (.classEq Q (synCplc (.cv u) (.cv n))))
      (.classEq Q (synCplc (.cv u) (.cv n))) p0162 p0170 p0171
  have p0173 := @gNe0i (.cv u) (synCpw (.cv g))
  have p0174 :=
    @gSyl
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem (synCpw (.cv g)) (.cv u)) (synWne (.cv u) (synC0)) p0152 p0173
  have p0175 := (Nominal.biimpRefl (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
  have p0176 := @gSsdif0 (synCpw (.cv b)) (synCpw (.cv g))
  have p0177 := @gEqss (synCpw (.cv g)) (synCpw (.cv b))
  have p0178 :=
    @gSimplbi2 (.classEq (synCpw (.cv g)) (synCpw (.cv b)))
      (synWss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWss (synCpw (.cv b)) (synCpw (.cv g))) p0177
  have p0179 :=
    @gSyl5bir (.classEq (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0))
      (synWss (synCpw (.cv b)) (synCpw (.cv g)))
      (synWss (synCpw (.cv g)) (synCpw (.cv b)))
      (.classEq (synCpw (.cv g)) (synCpw (.cv b))) p0176 p0178
  have p0180 :=
    @gNecon3d (synWss (synCpw (.cv g)) (synCpw (.cv b)))
      (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0) (synCpw (.cv g))
      (synCpw (.cv b)) p0179
  have p0181 :=
    @gImp (synWss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWne (synCpw (.cv g)) (synCpw (.cv b)))
      (synWne (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0)) p0180
  have p0182 :=
    @gSylbi (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWa (synWss (synCpw (.cv g)) (synCpw (.cv b)))
        (synWne (synCpw (.cv g)) (synCpw (.cv b))))
      (synWne (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0)) p0175 p0181
  have p0183 :=
    @gSyl
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWne (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0)) p0147 p0182
  have p0184 := @gEleq2 (.cv n) (synC0c) (synCdif (synCpw (.cv b)) (synCpw (.cv g)))
  have p0185 :=
    @gBiimpcd (.classEq (.cv n) (synC0c))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0c)) p0184
  have p0186 := @gEl0c (synCdif (synCpw (.cv b)) (synCpw (.cv g)))
  have p0187 :=
    @gSyl6ib (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
      (.classEq (.cv n) (synC0c))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0c))
      (.classEq (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0)) p0185 p0186
  have p0188 :=
    @gNecon3ad (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
      (.classEq (.cv n) (synC0c)) (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0)
      p0187
  have p0189 :=
    @gSylc
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
      (synWne (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synC0))
      (.neg (.classEq (.cv n) (synC0c))) p0153 p0183 p0188
  have p0190 := @gNnc0suc m (.cv n) dv_cache_0031
  have p0191 :=
    @gSylib
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem (.cv n) (synCnnc))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))))
      p0166 p0190
  have p0192 :=
    @gOrel1 (.classEq (.cv n) (synC0c))
      (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c))))
  have p0193 :=
    @gSylc
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.neg (.classEq (.cv n) (synC0c)))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))))
      (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))) p0189 p0191
      p0192
  have p0194 := @gAddceq2 (.cv n) (synCplc (.cv m) (synC1c)) (.cv u)
  have p0195 := @gAddcass (.cv u) (.cv m) (synC1c)
  have p0196 :=
    @gSyl6eqr (.classEq (.cv n) (synCplc (.cv m) (synC1c))) (synCplc (.cv u) (.cv n))
      (synCplc (.cv u) (synCplc (.cv m) (synC1c)))
      (synCplc (synCplc (.cv u) (.cv m)) (synC1c)) p0194 p0195
  have p0197 :=
    @gReximi (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
      (.classEq (synCplc (.cv u) (.cv n)) (synCplc (synCplc (.cv u) (.cv m)) (synC1c)))
      m (synCnnc) p0196
  have p0198 :=
    @gSyl
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c))))
      (synWrex m (synCnnc) (.classEq (synCplc (.cv u) (.cv n))
          (synCplc (synCplc (.cv u) (.cv m)) (synC1c))))
      p0193 p0197
  have p0199 := @gVex u
  have p0200 := @gVex n
  have p0201 := @gAddcex (.cv u) (.cv n) p0199 p0200
  have p0202 :=
    @gOpkltfing m (.cv u) (synCplc (.cv u) (.cv n)) (synCvv) (synCvv) dv_cache_0032
      dv_cache_0033
  have p0203 :=
    @gMp2an (.classMem (.cv u) (synCvv))
      (.classMem (synCplc (.cv u) (.cv n)) (synCvv))
      (synWb (.classMem (synCopk (.cv u) (synCplc (.cv u) (.cv n))) (synCltfin))
        (synWa (synWne (.cv u) (synC0)) (synWrex m (synCnnc)
            (.classEq (synCplc (.cv u) (.cv n))
              (synCplc (synCplc (.cv u) (.cv m)) (synC1c))))))
      p0199 p0201 p0202
  have p0204 :=
    @gSylanbrc
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (synWne (.cv u) (synC0))
      (synWrex m (synCnnc) (.classEq (synCplc (.cv u) (.cv n))
          (synCplc (synCplc (.cv u) (.cv m)) (synC1c))))
      (.classMem (synCopk (.cv u) (synCplc (.cv u) (.cv n))) (synCltfin)) p0174 p0198
      p0203
  have p0205 := @gOpkeq2 Q (synCplc (.cv u) (.cv n)) (.cv u)
  have p0206 :=
    @gEleq1d (.classEq Q (synCplc (.cv u) (.cv n))) (synCopk (.cv u) Q)
      (synCopk (.cv u) (synCplc (.cv u) (.cv n))) (synCltfin) p0205
  have p0207 :=
    @gSyl5ibrcom
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classMem (synCopk (.cv u) Q) (synCltfin))
      (.classEq Q (synCplc (.cv u) (.cv n)))
      (.classMem (synCopk (.cv u) (synCplc (.cv u) (.cv n))) (synCltfin)) p0204 p0206
  have p0208 :=
    @gMpd
      (synW3a (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))) (synWa (.classMem (.cv n) (synCnnc))
          (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))))
      (.classEq Q (synCplc (.cv u) (.cv n)))
      (.classMem (synCopk (.cv u) Q) (synCltfin)) p0172 p0207
  have p0209 :=
    @gN3expa
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))) (synWpss (synCpw (.cv g)) (synCpw (.cv b))))
      (synWa (.classMem (.cv n) (synCnnc))
        (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n)))
      (.classMem (synCopk (.cv u) Q) (synCltfin)) p0208
  have p0210 :=
    @gExp32
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (.cv n) (synCnnc))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
      (.classMem (synCopk (.cv u) Q) (synCltfin)) p0209
  have p0211 :=
    @gRexlimdv
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n))
      (.classMem (synCopk (.cv u) Q) (synCltfin)) n (synCnnc) dv_cache_0034
      dv_cache_0035 p0210
  have p0212 :=
    @gSyl5bi (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCfin))
      (synWrex n (synCnnc) (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (.cv n)))
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (synCopk (.cv u) Q) (synCltfin)) p0141 p0211
  have p0213 :=
    @gMpd
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (synCdif (synCpw (.cv b)) (synCpw (.cv g))) (synCfin))
      (.classMem (synCopk (.cv u) Q) (synCltfin)) p0140 p0212
  have p0214 := @gOpkeq1 (.cv u) N Q
  have p0215 :=
    @gEleq1d (.classEq (.cv u) N) (synCopk (.cv u) Q) (synCopk N Q) (synCltfin) p0214
  have p0216 :=
    @gSyl5ibcom
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classMem (synCopk (.cv u) Q) (synCltfin)) (.classEq (.cv u) N)
      (.classMem (synCopk N Q) (synCltfin)) p0213 p0215
  have p0217 :=
    @gMpd
      (synWa (synWa (synW3a
            (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
              (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
                (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
                (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
            (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
              (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
              (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
          (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
            (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
        (synW3a (.classMem (.cv u) (synCnnc)) (synWa (.classMem (synCpw (.cv a)) (.cv u))
            (.classMem (synCpw (.cv g)) (.cv u)))
          (synWpss (synCpw (.cv g)) (synCpw (.cv b)))))
      (.classEq (.cv u) N) (.classMem (synCopk N Q) (synCltfin)) p0122 p0216
  have p0218 :=
    @gN3exp2
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (.cv u) (synCnnc))
      (synWa (.classMem (synCpw (.cv a)) (.cv u)) (.classMem (synCpw (.cv g)) (.cv u)))
      (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
      (.classMem (synCopk N Q) (synCltfin)) p0217
  have p0219 :=
    @gRexlimdv
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synWa (.classMem (synCpw (.cv a)) (.cv u)) (.classMem (synCpw (.cv g)) (.cv u)))
      (.imp (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
        (.classMem (synCopk N Q) (synCltfin)))
      u (synCnnc) dv_cache_0036 dv_cache_0037 p0218
  have p0220 :=
    @gMpd
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synWrex u (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv u))
          (.classMem (synCpw (.cv g)) (.cv u))))
      (.imp (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
        (.classMem (synCopk N Q) (synCltfin)))
      p0107 p0219
  have p0221 :=
    @gSyl5
      (synWa (synWss (synCpw (.cv g)) (synCpw (.cv b)))
        (synWa (.classMem (synCsn (.cv x)) (synCpw (.cv b)))
          (.neg (.classMem (synCsn (.cv x)) (synCpw (.cv g))))))
      (synWpss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (synCopk N Q) (synCltfin)) p0100 p0220
  have p0222 :=
    @gMpand
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synWss (synCpw (.cv g)) (synCpw (.cv b)))
      (synWa (.classMem (synCsn (.cv x)) (synCpw (.cv b)))
        (.neg (.classMem (synCsn (.cv x)) (synCpw (.cv g)))))
      (.classMem (synCopk N Q) (synCltfin)) p0093 p0221
  have p0223 :=
    @gSyl5bir (synWa (.objMem x b) (.neg (.objMem x g)))
      (synWa (.classMem (synCsn (.cv x)) (synCpw (.cv b)))
        (.neg (.classMem (synCsn (.cv x)) (synCpw (.cv g)))))
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (synCopk N Q) (synCltfin)) p0086 p0222
  have p0224 :=
    @gSyld
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.objMem x d) (synWa (.objMem x b) (.neg (.objMem x g)))
      (.classMem (synCopk N Q) (synCltfin)) p0081 p0223
  have p0225 :=
    @gExlimdv
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.objMem x d) (.classMem (synCopk N Q) (synCltfin)) x dv_cache_0038 dv_cache_0039
      p0224
  have p0226_e00_recanon :
    Nominal.NPrf (synWb (synWne (.cv d) (synC0)) (synWex x (.objMem x d))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv synWex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0071
  have p0226 :=
    @gSyl5bi (synWne (.cv d) (synC0)) (synWex x (.objMem x d))
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (.classMem (synCopk N Q) (synCltfin)) p0226_e00_recanon p0225
  have p0227 :=
    @gMpd
      (synWa (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
        (synWa (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synWne (.cv d) (synC0)) (.classMem (synCopk N Q) (synCltfin)) p0070 p0226
  have p0228 :=
    @gExp32
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (synWa (.objMem g r) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
      (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
        (.classEq (.cv b) (synCun (.cv g) (.cv d))))
      (.classMem (synCopk N Q) (synCltfin)) p0227
  have p0229_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
              (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
              (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
          (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
            (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
            (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))) (.imp
          (synWa (.classMem (.cv g) (.cv r)) (.classMem (.cv d) (synCplc (.cv t) (synC1c))))
          (.imp (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
              (.classEq (.cv b) (synCun (.cv g) (.cv d))))
            (.classMem (synCopk N Q) (synCltfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCopk synCpr synCun synCnin synWnan synCcompl
          synCsn synCltfin synWex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0228
  have p0229 :=
    @gRexlimdvv
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
        (.classEq (.cv b) (synCun (.cv g) (.cv d))))
      (.classMem (synCopk N Q) (synCltfin)) g d (.cv r) (synCplc (.cv t) (synC1c))
      dv_cache_0021 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0024
      p0229_e00_recanon
  have p0230 :=
    @gSyl5bi (.classMem (.cv b) (synCplc (.cv r) (synCplc (.cv t) (synC1c))))
      (synWrex g (.cv r) (synWrex d (synCplc (.cv t) (synC1c))
          (synWa (.classEq (synCin (.cv g) (.cv d)) (synC0))
            (.classEq (.cv b) (synCun (.cv g) (.cv d))))))
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem (synCopk N Q) (synCltfin)) p0063 p0229
  have p0231 :=
    @gMpd
      (synW3a (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))) (synWa (.classMem (.cv t) (synCnnc))
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem (.cv b) (synCplc (.cv r) (synCplc (.cv t) (synC1c))))
      (.classMem (synCopk N Q) (synCltfin)) p0062 p0230
  have p0232 :=
    @gN3expa
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
        (synWa (.objMem a r) (.objMem b s)))
      (synWa (.classMem (.cv t) (synCnnc))
        (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
      (.classMem (synCopk N Q) (synCltfin)) p0231
  have p0233 :=
    @gExp32
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (.cv t) (synCnnc))
      (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))
      (.classMem (synCopk N Q) (synCltfin)) p0232
  have p0234 :=
    @gRexlimdv
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))
      (.classMem (synCopk N Q) (synCltfin)) t (synCnnc) dv_cache_0044 dv_cache_0045
      p0233
  have p0235 :=
    @gAdantld
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (synWrex t (synCnnc) (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c))))
      (.classMem (synCopk N Q) (synCltfin)) (synWne (.cv r) (synC0)) p0234
  have p0236 :=
    @gSylbid
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (synCopk (.cv r) (.cv s)) (synCltfin))
      (synWa (synWne (.cv r) (synC0)) (synWrex t (synCnnc)
          (.classEq (.cv s) (synCplc (synCplc (.cv r) (.cv t)) (synC1c)))))
      (.classMem (synCopk N Q) (synCltfin)) p0057 p0235
  have p0237 :=
    @gSylbird
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classMem (synCopk (synCtfin (.cv r)) (synCtfin (.cv s))) (synCltfin))
      (.classMem (synCopk (.cv r) (.cv s)) (synCltfin))
      (.classMem (synCopk N Q) (synCltfin)) p0055 p0236
  have p0238 := @gOpkeq12 M P (synCtfin (.cv r)) (synCtfin (.cv s))
  have p0239 :=
    @gEleq1d (synWa (.classEq M (synCtfin (.cv r))) (.classEq P (synCtfin (.cv s))))
      (synCopk M P) (synCopk (synCtfin (.cv r)) (synCtfin (.cv s))) (synCltfin) p0238
  have p0240 :=
    @gImbi1d (synWa (.classEq M (synCtfin (.cv r))) (.classEq P (synCtfin (.cv s))))
      (.classMem (synCopk M P) (synCltfin))
      (.classMem (synCopk (synCtfin (.cv r)) (synCtfin (.cv s))) (synCltfin))
      (.classMem (synCopk N Q) (synCltfin)) p0239
  have p0241 :=
    @gSyl5ibrcom
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      (synWa (.classEq M (synCtfin (.cv r))) (.classEq P (synCtfin (.cv s))))
      (.imp (.classMem (synCopk (synCtfin (.cv r)) (synCtfin (.cv s))) (synCltfin))
        (.classMem (synCopk N Q) (synCltfin)))
      p0237 p0240
  have p0242 :=
    @gMp2and
      (synWa (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
        (synWa (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
          (synWa (.objMem a r) (.objMem b s))))
      (.classEq M (synCtfin (.cv r))) (.classEq P (synCtfin (.cv s)))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0034 p0053 p0241
  have p0243 :=
    @gExp32
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
      (synWa (.objMem a r) (.objMem b s))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0242
  have p0244 :=
    @gSyl7
      (synWa (synWa (.objMem a r) (.objMem a r)) (synWa (.objMem b s) (.objMem b s)))
      (synWa (.objMem a r) (.objMem b s))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (.classMem (.cv r) (synCnnc)) (.classMem (.cv s) (synCnnc)))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0015 p0243
  have p0245 :=
    @gRexlimdvv
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWa (synWa (.objMem a r) (.objMem a r)) (synWa (.objMem b s) (.objMem b s)))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      r s (synCnnc) (synCnnc) dv_cache_0009 dv_cache_0046 dv_cache_0047 dv_cache_0048
      dv_cache_0049 dv_cache_0013 p0244
  have p0246 :=
    @gSyl5bir
      (synWa (synWrex r (synCnnc) (synWa (.objMem a r) (.objMem a r)))
        (synWrex s (synCnnc) (synWa (.objMem b s) (.objMem b s))))
      (synWrex r (synCnnc) (synWrex s (synCnnc) (synWa (synWa (.objMem a r) (.objMem a r))
            (synWa (.objMem b s) (.objMem b s)))))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0012 p0245
  have p0247 :=
    @gMp2and
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
        (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWrex r (synCnnc) (synWa (.objMem a r) (.objMem a r)))
      (synWrex s (synCnnc) (synWa (.objMem b s) (.objMem b s)))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0007 p0011 p0246
  have p0248 :=
    @gN3expia (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
        (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0247
  have p0249 :=
    @gExlimdvv
      (synWa (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))))
      (synWa (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
        (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      a b dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 p0248
  have p0250 :=
    @gSyl5bir
      (synWa (synWex a
          (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))) (synWex b
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (synWex a (synWex b (synWa
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0003 p0249
  have p0251 :=
    @gN3impia (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
      (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc)))
      (synWa (synWex a
          (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))) (synWex b
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0250
  have p0252 :=
    @gSylbir
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWex a
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))))
        (synW3a (.classMem P (synCnnc)) (.classMem Q (synCnnc)) (synWex b
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem P (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem Q (synCnnc))) (synWa (synWex a
            (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N)))
          (synWex b
            (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q)))))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      p0002 p0251
  have p0253 :=
    @gSyl2anb (synWsfin M N)
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWex a
          (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))))
      (synW3a (.classMem P (synCnnc)) (.classMem Q (synCnnc)) (synWex b
          (synWa (.classMem (synCpw1 (.cv b)) P) (.classMem (synCpw (.cv b)) Q))))
      (.imp (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin)))
      (synWsfin P Q) p0000 p0001 p0252
  have p0254 :=
    @gImp (synWa (synWsfin M N) (synWsfin P Q))
      (.classMem (synCopk M P) (synCltfin)) (.classMem (synCopk N Q) (synCltfin))
      p0253
  exact p0254


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part019`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sfin111`. -/
@[expose]
noncomputable def gSfin111 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (synWa (synWsfin M P) (synWsfin N P)) (.classEq M N)) :=
  by
  let proofSupport : Finset Var := P.fv ∪ M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_P : a ∉ P.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : a ∉ (N).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_N, not_false_eq_true])
  have dv_cache_0002 : a ∉ (P).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_P, not_false_eq_true])
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
  have dv_cache_0004 : a ∉ ((synWne M (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_a_not_M, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin N P a
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gSimp2bi (synWsfin N P) (.classMem N (synCnnc)) (.classMem P (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) N) (.classMem (synCpw (.cv a)) P)))
      p0000
  have p0002 := @gAdantl (synWsfin N P) (.classMem P (synCnnc)) (synWsfin M P) p0001
  have p0003 := @gLtfinirr P
  have p0004 :=
    @gSyl (synWa (synWsfin M P) (synWsfin N P)) (.classMem P (synCnnc))
      (.neg (.classMem (synCopk P P) (synCltfin))) p0002 p0003
  have p0005 := @gSfinltfin N P M P
  have p0006 :=
    @gMtand (synWa (synWsfin M P) (synWsfin N P))
      (.classMem (synCopk M N) (synCltfin)) (.classMem (synCopk P P) (synCltfin))
      p0004 p0005
  have p0007 := @gSfinltfin M P N P
  have p0008 :=
    @gEx (synWa (synWsfin N P) (synWsfin M P)) (.classMem (synCopk N M) (synCltfin))
      (.classMem (synCopk P P) (synCltfin)) p0007
  have p0009 :=
    @gAncoms (synWsfin N P) (synWsfin M P)
      (.imp (.classMem (synCopk N M) (synCltfin)) (.classMem (synCopk P P) (synCltfin)))
      p0008
  have p0010 :=
    @gMtod (synWa (synWsfin M P) (synWsfin N P))
      (.classMem (synCopk N M) (synCltfin)) (.classMem (synCopk P P) (synCltfin))
      p0004 p0009
  have p0011 :=
    @gIoran (.classMem (synCopk M N) (synCltfin))
      (.classMem (synCopk N M) (synCltfin))
  have p0012 :=
    @gSylanbrc (synWa (synWsfin M P) (synWsfin N P))
      (.neg (.classMem (synCopk M N) (synCltfin)))
      (.neg (.classMem (synCopk N M) (synCltfin)))
      (.neg (synWo (.classMem (synCopk M N) (synCltfin))
          (.classMem (synCopk N M) (synCltfin))))
      p0006 p0010 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin M P a
      dv_cache_0003 dv_cache_0002
  have p0014 :=
    @gSimp1bi (synWsfin M P) (.classMem M (synCnnc)) (.classMem P (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) P)))
      p0013
  have p0015 := @gAdantr (synWsfin M P) (.classMem M (synCnnc)) (synWsfin N P) p0014
  have p0016 :=
    @gSimp1bi (synWsfin N P) (.classMem N (synCnnc)) (.classMem P (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) N) (.classMem (synCpw (.cv a)) P)))
      p0000
  have p0017 := @gAdantl (synWsfin N P) (.classMem N (synCnnc)) (synWsfin M P) p0016
  have p0018 := @gNe0i M (synCpw1 (.cv a))
  have p0019 :=
    @gAdantr (.classMem (synCpw1 (.cv a)) M) (synWne M (synC0))
      (.classMem (synCpw (.cv a)) P) p0018
  have p0020 :=
    @gExlimiv (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) P))
      (synWne M (synC0)) a dv_cache_0004 p0019
  have p0021 :=
    @gN3ad2ant3
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) P)))
      (.classMem M (synCnnc)) (synWne M (synC0)) (.classMem P (synCnnc)) p0020
  have p0022 :=
    @gSylbi (synWsfin M P)
      (synW3a (.classMem M (synCnnc)) (.classMem P (synCnnc)) (synWex a
          (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) P))))
      (synWne M (synC0)) p0013 p0021
  have p0023 := @gAdantr (synWsfin M P) (synWne M (synC0)) (synWsfin N P) p0022
  have p0024 := @gLtfintri M N
  have p0025 :=
    @gSyl3anc (synWa (synWsfin M P) (synWsfin N P)) (.classMem M (synCnnc))
      (.classMem N (synCnnc)) (synWne M (synC0))
      (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
        (.classMem (synCopk N M) (synCltfin)))
      p0015 p0017 p0023 p0024
  have p0026 :=
    (Nominal.biimpRefl (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
        (.classMem (synCopk N M) (synCltfin))))
  have p0027 :=
    @gSylib (synWa (synWsfin M P) (synWsfin N P))
      (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
        (.classMem (synCopk N M) (synCltfin)))
      (synWo (synWo (.classMem (synCopk M N) (synCltfin)) (.classEq M N))
        (.classMem (synCopk N M) (synCltfin)))
      p0025 p0026
  have p0028 :=
    @gOr32 (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
      (.classMem (synCopk N M) (synCltfin))
  have p0029 :=
    @gSylib (synWa (synWsfin M P) (synWsfin N P))
      (synWo (synWo (.classMem (synCopk M N) (synCltfin)) (.classEq M N))
        (.classMem (synCopk N M) (synCltfin)))
      (synWo (synWo (.classMem (synCopk M N) (synCltfin))
          (.classMem (synCopk N M) (synCltfin))) (.classEq M N))
      p0027 p0028
  have p0030 :=
    @gOrel1
      (synWo (.classMem (synCopk M N) (synCltfin)) (.classMem (synCopk N M) (synCltfin)))
      (.classEq M N)
  have p0031 :=
    @gSylc (synWa (synWsfin M P) (synWsfin N P))
      (.neg (synWo (.classMem (synCopk M N) (synCltfin))
          (.classMem (synCopk N M) (synCltfin))))
      (synWo (synWo (.classMem (synCopk M N) (synCltfin))
          (.classMem (synCopk N M) (synCltfin))) (.classEq M N))
      (.classEq M N) p0012 p0029 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end
