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

@[expose]
noncomputable def g_sfinltfin (P : Class) (Q : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wsfin M N) (syn_wsfin P Q))
          (.classMem (syn_copk M P) (syn_cltfin))) (.classMem (syn_copk N Q) (syn_cltfin))) :=
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
    b ∉ ((syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))).fv :=
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
    a ∉ ((syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))).fv :=
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
  have dv_cache_0009 : s ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0010 : r ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0011 : s ∉ ((syn_wa (.objMem a r) (.objMem a r))).fv :=
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
  have dv_cache_0012 : r ∉ ((syn_wa (.objMem b s) (.objMem b s))).fv :=
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
  have dv_cache_0022 : g ∉ ((syn_cplc (.cv t) (syn_c1c))).fv :=
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
  have dv_cache_0023 : d ∉ ((syn_cplc (.cv t) (syn_c1c))).fv :=
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
  have dv_cache_0030 : n ∉ ((syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g)))).fv :=
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
  have dv_cache_0033 : m ∉ ((syn_cplc (.cv u) (.cv n))).fv :=
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
  have dv_cache_0034 : n ∉ ((Wff.classMem (syn_copk (.cv u) Q) (syn_cltfin))).fv :=
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
      ((syn_wa (syn_wa (syn_w3a
              (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
                (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                  (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                  (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
              (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
                (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
                (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))) (syn_wa
              (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
              (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
                (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
          (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
              (.classMem (syn_cpw (.cv g)) (.cv u)))
            (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))).fv :=
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
      ((Wff.imp (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
          (.classMem (syn_copk N Q) (syn_cltfin)))).fv :=
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
      ((syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))).fv :=
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
  have dv_cache_0038 : x ∉ ((Wff.classMem (syn_copk N Q) (syn_cltfin))).fv :=
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
      ((syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))).fv :=
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
  have dv_cache_0040 : g ∉ ((Wff.classMem (syn_copk N Q) (syn_cltfin))).fv :=
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
  have dv_cache_0041 : d ∉ ((Wff.classMem (syn_copk N Q) (syn_cltfin))).fv :=
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
      ((syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))).fv :=
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
      ((syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))).fv :=
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
  have dv_cache_0044 : t ∉ ((Wff.classMem (syn_copk N Q) (syn_cltfin))).fv :=
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
      ((syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))))).fv :=
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
      ((Wff.imp (.classMem (syn_copk M P) (syn_cltfin))
          (.classMem (syn_copk N Q) (syn_cltfin)))).fv :=
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
      ((Wff.imp (.classMem (syn_copk M P) (syn_cltfin))
          (.classMem (syn_copk N Q) (syn_cltfin)))).fv :=
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
      ((syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))).fv :=
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
      ((syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))).fv :=
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
      ((Wff.imp (.classMem (syn_copk M P) (syn_cltfin))
          (.classMem (syn_copk N Q) (syn_cltfin)))).fv :=
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
      ((Wff.imp (.classMem (syn_copk M P) (syn_cltfin))
          (.classMem (syn_copk N Q) (syn_cltfin)))).fv :=
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
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))))).fv :=
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
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M N a
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin P Q b
      dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_n_3an6 (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem Q (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N)))
      (syn_wex b (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
  have p0003 :=
    @g_eeanv (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
      (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)) a b
      dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_simp1l (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
  have p0005 :=
    @g_simp3ll (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N)
      (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
  have p0006 := @g_ncfinlower (.cv a) (.cv a) r M dv_cache_0007 dv_cache_0007
  have p0007_e03_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) M)
          (.classMem (syn_cpw1 (.cv a)) M))
        (syn_wrex r (syn_cnnc) (syn_wa (.objMem a r) (.objMem a r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_cpw1 syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wrex
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
    @g_syl3anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) M)
      (.classMem (syn_cpw1 (.cv a)) M)
      (syn_wrex r (syn_cnnc) (syn_wa (.objMem a r) (.objMem a r))) p0004 p0005 p0005
      p0007_e03_recanon
  have p0008 :=
    @g_simp1r (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
  have p0009 :=
    @g_simp3rl (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)
      (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
  have p0010 := @g_ncfinlower (.cv b) (.cv b) s P dv_cache_0008 dv_cache_0008
  have p0011_e03_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem P (syn_cnnc)) (.classMem (syn_cpw1 (.cv b)) P)
          (.classMem (syn_cpw1 (.cv b)) P))
        (syn_wrex s (syn_cnnc) (syn_wa (.objMem b s) (.objMem b s)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_cpw1 syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wrex
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
    @g_syl3anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.classMem P (syn_cnnc)) (.classMem (syn_cpw1 (.cv b)) P)
      (.classMem (syn_cpw1 (.cv b)) P)
      (syn_wrex s (syn_cnnc) (syn_wa (.objMem b s) (.objMem b s))) p0008 p0009 p0009
      p0011_e03_recanon
  have p0012 :=
    @g_reeanv (syn_wa (.objMem a r) (.objMem a r)) (syn_wa (.objMem b s) (.objMem b s)) r
      s (syn_cnnc) (syn_cnnc) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0013 := @g_simpl (.objMem a r) (.objMem a r)
  have p0014 := @g_simpl (.objMem b s) (.objMem b s)
  have p0015 :=
    @g_anim12i (syn_wa (.objMem a r) (.objMem a r)) (.objMem a r)
      (syn_wa (.objMem b s) (.objMem b s)) (.objMem b s) p0013 p0014
  have p0016 :=
    @g_adantr
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.classMem (syn_cpw1 (.cv a)) M)
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
      p0005
  have p0017 :=
    @g_simprll
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc))
      (syn_wa (.objMem a r) (.objMem b s))
  have p0018 :=
    @g_simprrl
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc))) (.objMem a r)
      (.objMem b s)
  have p0019 := @g_tfinpw1 (.cv a) (.cv r)
  have p0020_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv r) (syn_cnnc)) (.objMem a r))
        (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (.cv r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan
          syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_ctfin syn_cif syn_wo syn_c0 syn_cdif
          syn_cvv syn_cio syn_cuni
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
    @g_syl2anc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (.cv r) (syn_cnnc)) (.objMem a r)
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (.cv r))) p0017 p0018 p0020_e02_recanon
  have p0021 := @g_elin (syn_cpw1 (.cv a)) M (syn_ctfin (.cv r))
  have p0022 :=
    @g_sylanbrc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (.cv r)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cin M (syn_ctfin (.cv r)))) p0016 p0020 p0021
  have p0023 := @g_n0i (syn_cin M (syn_ctfin (.cv r))) (syn_cpw1 (.cv a))
  have p0024 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cin M (syn_ctfin (.cv r))))
      (.neg (.classEq (syn_cin M (syn_ctfin (.cv r))) (syn_c0))) p0022 p0023
  have p0025 :=
    @g_simpl1l (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
  have p0026 := @g_ne0i (.cv r) (.cv a)
  have p0027_e01_recanon : Nominal.NPrf (.imp (.objMem a r) (syn_wne (.cv r) (syn_c0))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.objMem a r) (syn_wne (.cv r) (syn_c0)) p0018 p0027_e01_recanon
  have p0028 := @g_tfinprop (.cv r) a dv_cache_0014
  have p0029 :=
    @g_simpld (syn_wa (.classMem (.cv r) (syn_cnnc)) (syn_wne (.cv r) (syn_c0)))
      (.classMem (syn_ctfin (.cv r)) (syn_cnnc))
      (syn_wrex a (.cv r) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (.cv r)))) p0028
  have p0030 :=
    @g_syl2anc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (.cv r) (syn_cnnc)) (syn_wne (.cv r) (syn_c0))
      (.classMem (syn_ctfin (.cv r)) (syn_cnnc)) p0017 p0027 p0029
  have p0031 := @g_nndisjeq M (syn_ctfin (.cv r))
  have p0032 :=
    @g_syl2anc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem M (syn_cnnc)) (.classMem (syn_ctfin (.cv r)) (syn_cnnc))
      (syn_wo (.classEq (syn_cin M (syn_ctfin (.cv r))) (syn_c0))
        (.classEq M (syn_ctfin (.cv r))))
      p0025 p0030 p0031
  have p0033 :=
    @g_orel1 (.classEq (syn_cin M (syn_ctfin (.cv r))) (syn_c0))
      (.classEq M (syn_ctfin (.cv r)))
  have p0034 :=
    @g_sylc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.neg (.classEq (syn_cin M (syn_ctfin (.cv r))) (syn_c0)))
      (syn_wo (.classEq (syn_cin M (syn_ctfin (.cv r))) (syn_c0))
        (.classEq M (syn_ctfin (.cv r))))
      (.classEq M (syn_ctfin (.cv r))) p0024 p0032 p0033
  have p0035 :=
    @g_adantr
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.classMem (syn_cpw1 (.cv b)) P)
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
      p0009
  have p0036 :=
    @g_simprlr
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc))
      (syn_wa (.objMem a r) (.objMem b s))
  have p0037 :=
    @g_simprrr
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc))) (.objMem a r)
      (.objMem b s)
  have p0038 := @g_tfinpw1 (.cv b) (.cv s)
  have p0039_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv s) (syn_cnnc)) (.objMem b s))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin (.cv s)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan
          syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_ctfin syn_cif syn_wo syn_c0 syn_cdif
          syn_cvv syn_cio syn_cuni
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
    @g_syl2anc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (.cv s) (syn_cnnc)) (.objMem b s)
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin (.cv s))) p0036 p0037 p0039_e02_recanon
  have p0040 := @g_elin (syn_cpw1 (.cv b)) P (syn_ctfin (.cv s))
  have p0041 :=
    @g_sylanbrc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin (.cv s)))
      (.classMem (syn_cpw1 (.cv b)) (syn_cin P (syn_ctfin (.cv s)))) p0035 p0039 p0040
  have p0042 := @g_n0i (syn_cin P (syn_ctfin (.cv s))) (syn_cpw1 (.cv b))
  have p0043 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (syn_cpw1 (.cv b)) (syn_cin P (syn_ctfin (.cv s))))
      (.neg (.classEq (syn_cin P (syn_ctfin (.cv s))) (syn_c0))) p0041 p0042
  have p0044 :=
    @g_simpl1r (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
  have p0045 := @g_ne0i (.cv s) (.cv b)
  have p0046_e01_recanon : Nominal.NPrf (.imp (.objMem b s) (syn_wne (.cv s) (syn_c0))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0045
  have p0046 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.objMem b s) (syn_wne (.cv s) (syn_c0)) p0037 p0046_e01_recanon
  have p0047 := @g_tfinprop (.cv s) a dv_cache_0015
  have p0048 :=
    @g_simpld (syn_wa (.classMem (.cv s) (syn_cnnc)) (syn_wne (.cv s) (syn_c0)))
      (.classMem (syn_ctfin (.cv s)) (syn_cnnc))
      (syn_wrex a (.cv s) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (.cv s)))) p0047
  have p0049 :=
    @g_syl2anc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (.cv s) (syn_cnnc)) (syn_wne (.cv s) (syn_c0))
      (.classMem (syn_ctfin (.cv s)) (syn_cnnc)) p0036 p0046 p0048
  have p0050 := @g_nndisjeq P (syn_ctfin (.cv s))
  have p0051 :=
    @g_syl2anc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem P (syn_cnnc)) (.classMem (syn_ctfin (.cv s)) (syn_cnnc))
      (syn_wo (.classEq (syn_cin P (syn_ctfin (.cv s))) (syn_c0))
        (.classEq P (syn_ctfin (.cv s))))
      p0044 p0049 p0050
  have p0052 :=
    @g_orel1 (.classEq (syn_cin P (syn_ctfin (.cv s))) (syn_c0))
      (.classEq P (syn_ctfin (.cv s)))
  have p0053 :=
    @g_sylc
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.neg (.classEq (syn_cin P (syn_ctfin (.cv s))) (syn_c0)))
      (syn_wo (.classEq (syn_cin P (syn_ctfin (.cv s))) (syn_c0))
        (.classEq P (syn_ctfin (.cv s))))
      (.classEq P (syn_ctfin (.cv s))) p0043 p0051 p0052
  have p0054 := @g_tfinltfin (.cv r) (.cv s)
  have p0055 :=
    @g_ad2antrl (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
      (syn_wb (.classMem (syn_copk (.cv r) (.cv s)) (syn_cltfin))
        (.classMem (syn_copk (syn_ctfin (.cv r)) (syn_ctfin (.cv s))) (syn_cltfin)))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.objMem a r) (.objMem b s)) p0054
  have p0056 :=
    @g_opkltfing t (.cv r) (.cv s) (syn_cnnc) (syn_cnnc) dv_cache_0016 dv_cache_0017
  have p0057 :=
    @g_ad2antrl (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
      (syn_wb (.classMem (syn_copk (.cv r) (.cv s)) (syn_cltfin))
        (syn_wa (syn_wne (.cv r) (syn_c0)) (syn_wrex t (syn_cnnc)
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.objMem a r) (.objMem b s)) p0056
  have p0058 :=
    @g_simp2rr (.objMem a r) (.objMem b s)
      (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.classMem (.cv t) (syn_cnnc))
        (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
  have p0059 :=
    @g_simp3r
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
      (.classMem (.cv t) (syn_cnnc))
      (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))
  have p0060_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (.classMem (.cv b) (.cv s))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _)
      p0058
  have p0060 :=
    @g_eleqtrd
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.cv b) (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)) p0060_e00_recanon
      p0059
  have p0061 := @g_addcass (.cv r) (.cv t) (syn_c1c)
  have p0062 :=
    @g_syl6eleq
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.cv b) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))
      (syn_cplc (.cv r) (syn_cplc (.cv t) (syn_c1c))) p0060 p0061
  have p0063 :=
    @g_eladdc (.cv b) (.cv r) (syn_cplc (.cv t) (syn_c1c)) g d dv_cache_0018 dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0064 := @g_n_0nelsuc (.cv t)
  have p0065 :=
    @g_simprlr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c)))
      (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
        (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))
  have p0066 := @g_eleq1 (.cv d) (syn_c0) (syn_cplc (.cv t) (syn_c1c))
  have p0067 :=
    @g_syl5ibcom
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))) (.classEq (.cv d) (syn_c0))
      (.classMem (syn_c0) (syn_cplc (.cv t) (syn_c1c))) p0065 p0066
  have p0068 :=
    @g_mtoi
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classEq (.cv d) (syn_c0)) (.classMem (syn_c0) (syn_cplc (.cv t) (syn_c1c))) p0064
      p0067
  have p0069 := (Nominal.biimpRefl (syn_wne (.cv d) (syn_c0)))
  have p0070 :=
    @g_sylibr
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.neg (.classEq (.cv d) (syn_c0))) (syn_wne (.cv d) (syn_c0)) p0068 p0069
  have p0071 := @g_n0 x (.cv d) dv_cache_0025
  have p0072 := @g_ssun2 (.cv d) (.cv g)
  have p0073 := @g_sseq2 (.cv b) (syn_cun (.cv g) (.cv d)) (.cv d)
  have p0074 :=
    @g_mpbiri (.classEq (.cv b) (syn_cun (.cv g) (.cv d))) (syn_wss (.cv d) (.cv b))
      (syn_wss (.cv d) (syn_cun (.cv g) (.cv d))) p0072 p0073
  have p0075 :=
    @g_sseld (.classEq (.cv b) (syn_cun (.cv g) (.cv d))) (.cv d) (.cv b) (.cv x) p0074
  have p0076 := @g_disjr x (.cv g) (.cv d) dv_cache_0026 dv_cache_0025
  have p0077 := @g_rsp (.neg (.objMem x g)) x (.cv d)
  have p0078_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
        (syn_wral x (.cv d) (.neg (.objMem x g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_c0 syn_cdif syn_cvv
          syn_wral
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
      (.imp (syn_wral x (.cv d) (.neg (.objMem x g)))
        (.imp (.objMem x d) (.neg (.objMem x g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wral
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0078 :=
    @g_sylbi (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
      (syn_wral x (.cv d) (.neg (.objMem x g))) (.imp (.objMem x d) (.neg (.objMem x g)))
      p0078_e00_recanon p0078_e01_recanon
  have p0079_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (syn_cun (.cv g) (.cv d))) (.imp (.objMem x d) (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cun syn_cnin syn_wnan syn_wa syn_ccompl
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0075
  have p0079 :=
    @g_anim12ii (.classEq (.cv b) (syn_cun (.cv g) (.cv d))) (.objMem x d) (.objMem x b)
      (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0)) (.neg (.objMem x g)) p0079_e00_recanon
      p0078
  have p0080 :=
    @g_ancoms (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))
      (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
      (.imp (.objMem x d) (syn_wa (.objMem x b) (.neg (.objMem x g)))) p0079
  have p0081 :=
    @g_ad2antll
      (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
        (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))
      (.imp (.objMem x d) (syn_wa (.objMem x b) (.neg (.objMem x g))))
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c)))) p0080
  have p0082 := @g_vex x
  have p0083 := @g_snelpw (.cv x) (.cv b) p0082
  have p0084 := @g_snelpw (.cv x) (.cv g) p0082
  have p0085_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g))) (.objMem x g)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
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
    @g_notbii (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g))) (.objMem x g)
      p0085_e00_recanon
  have p0086_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b))) (.objMem x b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
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
    @g_anbi12i (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b))) (.objMem x b)
      (.neg (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g)))) (.neg (.objMem x g))
      p0086_e00_recanon p0085
  have p0087 := @g_ssun1 (.cv g) (.cv d)
  have p0088 := @g_sseq2 (.cv b) (syn_cun (.cv g) (.cv d)) (.cv g)
  have p0089 :=
    @g_mpbiri (.classEq (.cv b) (syn_cun (.cv g) (.cv d))) (syn_wss (.cv g) (.cv b))
      (syn_wss (.cv g) (syn_cun (.cv g) (.cv d))) p0087 p0088
  have p0090 := @g_sspwb (.cv g) (.cv b)
  have p0091 :=
    @g_sylib (.classEq (.cv b) (syn_cun (.cv g) (.cv d))) (syn_wss (.cv g) (.cv b))
      (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b))) p0089 p0090
  have p0092 :=
    @g_adantl (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))
      (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0)) p0091
  have p0093 :=
    @g_ad2antll
      (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
        (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))
      (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c)))) p0092
  have p0094 := @g_eleq2 (syn_cpw (.cv g)) (syn_cpw (.cv b)) (syn_csn (.cv x))
  have p0095 :=
    @g_biimprcd (.classEq (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g)))
      (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b))) p0094
  have p0096 :=
    @g_con3d (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b)))
      (.classEq (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g))) p0095
  have p0097 :=
    @g_imp (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b)))
      (.neg (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g))))
      (.neg (.classEq (syn_cpw (.cv g)) (syn_cpw (.cv b)))) p0096
  have p0098 :=
    @g_anim2i
      (syn_wa (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b)))
        (.neg (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g)))))
      (.neg (.classEq (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b))) p0097
  have p0099 := @g_dfpss2 (syn_cpw (.cv g)) (syn_cpw (.cv b))
  have p0100 :=
    @g_sylibr
      (syn_wa (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
        (syn_wa (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b)))
          (.neg (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g))))))
      (syn_wa (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
        (.neg (.classEq (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))) p0098 p0099
  have p0101 :=
    @g_simp2ll (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc))
      (syn_wa (.objMem a r) (.objMem b s))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.classMem (.cv t) (syn_cnnc))
        (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
  have p0102 :=
    @g_adantr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem (.cv r) (syn_cnnc))
      (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
        (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
          (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))))
      p0101
  have p0103 :=
    @g_simp2rl (.objMem a r) (.objMem b s)
      (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.classMem (.cv t) (syn_cnnc))
        (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
  have p0104 :=
    @g_adantr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.objMem a r)
      (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
        (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
          (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))))
      p0103
  have p0105 :=
    @g_simprll
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c)))
      (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
        (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))
  have p0106 :=
    @g_nnpweq (.cv a) (.cv g) u (.cv r) dv_cache_0027 dv_cache_0028 dv_cache_0029
  have p0107_e03_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (.cv r) (syn_cnnc)) (.objMem a r) (.objMem g r))
        (syn_wrex u (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_wrex syn_wex
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
    @g_syl3anc
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (.cv r) (syn_cnnc)) (.objMem a r) (.objMem g r)
      (syn_wrex u (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))))
      p0102 p0104 p0105 p0107_e03_recanon
  have p0108 :=
    @g_simpr2l (.classMem (syn_cpw (.cv a)) (.cv u)) (.classMem (syn_cpw (.cv g)) (.cv u))
      (.classMem (.cv u) (syn_cnnc)) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
  have p0109 :=
    @g_simp3lr (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N)
      (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
  have p0110 :=
    @g_n_3ad2ant1
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
      (.classMem (syn_cpw (.cv a)) N)
      (syn_wa (.classMem (.cv t) (syn_cnnc))
        (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
      p0109
  have p0111 :=
    @g_ad2antrr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem (syn_cpw (.cv a)) N)
      (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
        (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
          (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      p0110
  have p0112 := @g_elin (syn_cpw (.cv a)) (.cv u) N
  have p0113 :=
    @g_sylanbrc
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (syn_cpw (.cv a)) (.cv u)) (.classMem (syn_cpw (.cv a)) N)
      (.classMem (syn_cpw (.cv a)) (syn_cin (.cv u) N)) p0108 p0111 p0112
  have p0114 := @g_n0i (syn_cin (.cv u) N) (syn_cpw (.cv a))
  have p0115 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (syn_cpw (.cv a)) (syn_cin (.cv u) N))
      (.neg (.classEq (syn_cin (.cv u) N) (syn_c0))) p0113 p0114
  have p0116 :=
    @g_simpr1
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (.cv u) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u)) (.classMem (syn_cpw (.cv g)) (.cv u)))
      (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
  have p0117 :=
    @g_simp12l (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
      (syn_wa (.classMem (.cv t) (syn_cnnc))
        (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
  have p0118 :=
    @g_ad2antrr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem N (syn_cnnc))
      (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
        (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
          (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      p0117
  have p0119 := @g_nndisjeq (.cv u) N
  have p0120 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (.cv u) (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wo (.classEq (syn_cin (.cv u) N) (syn_c0)) (.classEq (.cv u) N)) p0116 p0118
      p0119
  have p0121 := @g_orel1 (.classEq (syn_cin (.cv u) N) (syn_c0)) (.classEq (.cv u) N)
  have p0122 :=
    @g_sylc
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.neg (.classEq (syn_cin (.cv u) N) (syn_c0)))
      (syn_wo (.classEq (syn_cin (.cv u) N) (syn_c0)) (.classEq (.cv u) N))
      (.classEq (.cv u) N) p0115 p0120 p0121
  have p0123 :=
    @g_simp3rr (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)
      (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
  have p0124 :=
    @g_n_3ad2ant1
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
      (.classMem (syn_cpw (.cv b)) Q)
      (syn_wa (.classMem (.cv t) (syn_cnnc))
        (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
      p0123
  have p0125 :=
    @g_ad2antrr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem (syn_cpw (.cv b)) Q)
      (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
        (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
          (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      p0124
  have p0126 :=
    @g_simp12r (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
      (syn_wa (.classMem (.cv t) (syn_cnnc))
        (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
  have p0127 :=
    @g_ad2antrr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem Q (syn_cnnc))
      (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
        (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
          (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      p0126
  have p0128 := @g_elunii (syn_cpw (.cv b)) Q (syn_cnnc)
  have p0129 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (syn_cpw (.cv b)) Q) (.classMem Q (syn_cnnc))
      (.classMem (syn_cpw (.cv b)) (syn_cuni (syn_cnnc))) p0125 p0127 p0128
  have p0130 := (Nominal.classEqRefl (syn_cfin))
  have p0131 :=
    @g_syl6eleqr
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (syn_cpw (.cv b)) (syn_cuni (syn_cnnc)) (syn_cfin) p0129 p0130
  have p0132 := @g_vex b
  have p0133 := @g_pwex (.cv b) p0132
  have p0134 := @g_vex g
  have p0135 := @g_pwex (.cv g) p0134
  have p0136 := @g_difex (syn_cpw (.cv b)) (syn_cpw (.cv g)) p0133 p0135
  have p0137 := @g_difss (syn_cpw (.cv b)) (syn_cpw (.cv g))
  have p0138 :=
    @g_ssfin (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cpw (.cv b)) (syn_cvv)
  have p0139 :=
    @g_mp3an13 (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cvv))
      (.classMem (syn_cpw (.cv b)) (syn_cfin))
      (syn_wss (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cpw (.cv b)))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cfin)) p0136 p0137
      p0138
  have p0140 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (syn_cpw (.cv b)) (syn_cfin))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cfin)) p0131 p0139
  have p0141 := @g_elfin n (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) dv_cache_0030
  have p0142 :=
    @g_adantr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem (syn_cpw (.cv b)) Q)
      (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
        (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
          (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))))
      p0124
  have p0143 :=
    @g_n_3ad2ant1
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      (.classMem (syn_cpw (.cv b)) Q)
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n)))
      p0142
  have p0144 := @g_undif1 (syn_cpw (.cv b)) (syn_cpw (.cv g))
  have p0145 := @g_uncom (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cpw (.cv g))
  have p0146 :=
    @g_eqtr3i (syn_cun (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cpw (.cv g)))
      (syn_cun (syn_cpw (.cv b)) (syn_cpw (.cv g)))
      (syn_cun (syn_cpw (.cv g)) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g)))) p0144
      p0145
  have p0147 :=
    @g_simp23
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (.cv u) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u)) (.classMem (syn_cpw (.cv g)) (.cv u)))
      (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n)))
  have p0148 :=
    @g_pssssd
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (syn_cpw (.cv g)) (syn_cpw (.cv b)) p0147
  have p0149 := @g_ssequn2 (syn_cpw (.cv g)) (syn_cpw (.cv b))
  have p0150 :=
    @g_sylib
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (.classEq (syn_cun (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cpw (.cv b))) p0148
      p0149
  have p0151 :=
    @g_syl5eqr
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (syn_cun (syn_cpw (.cv g)) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))))
      (syn_cun (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cpw (.cv b)) p0146 p0150
  have p0152 :=
    @g_simp22r (.classMem (syn_cpw (.cv a)) (.cv u)) (.classMem (syn_cpw (.cv g)) (.cv u))
      (.classMem (.cv u) (syn_cnnc)) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n)))
  have p0153 :=
    @g_simp3r
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
  have p0154 := @g_disjdif (syn_cpw (.cv g)) (syn_cpw (.cv b))
  have p0155 :=
    @g_a1i
      (.classEq (syn_cin (syn_cpw (.cv g)) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))))
        (syn_c0))
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      p0154
  have p0156 :=
    @g_eladdci (syn_cpw (.cv g)) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv u)
      (.cv n)
  have p0157 :=
    @g_syl3anc
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem (syn_cpw (.cv g)) (.cv u))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
      (.classEq (syn_cin (syn_cpw (.cv g)) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))))
        (syn_c0))
      (.classMem (syn_cun (syn_cpw (.cv g)) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))))
        (syn_cplc (.cv u) (.cv n)))
      p0152 p0153 p0155 p0156
  have p0158 :=
    @g_eqeltrrd
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (syn_cun (syn_cpw (.cv g)) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))))
      (syn_cpw (.cv b)) (syn_cplc (.cv u) (.cv n)) p0151 p0157
  have p0159 := @g_elin (syn_cpw (.cv b)) Q (syn_cplc (.cv u) (.cv n))
  have p0160 :=
    @g_sylanbrc
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem (syn_cpw (.cv b)) Q)
      (.classMem (syn_cpw (.cv b)) (syn_cplc (.cv u) (.cv n)))
      (.classMem (syn_cpw (.cv b)) (syn_cin Q (syn_cplc (.cv u) (.cv n)))) p0143 p0158
      p0159
  have p0161 := @g_n0i (syn_cin Q (syn_cplc (.cv u) (.cv n))) (syn_cpw (.cv b))
  have p0162 :=
    @g_syl
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem (syn_cpw (.cv b)) (syn_cin Q (syn_cplc (.cv u) (.cv n))))
      (.neg (.classEq (syn_cin Q (syn_cplc (.cv u) (.cv n))) (syn_c0))) p0160 p0161
  have p0163 :=
    @g_adantr
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem Q (syn_cnnc))
      (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
        (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
          (.classEq (.cv b) (syn_cun (.cv g) (.cv d)))))
      p0126
  have p0164 :=
    @g_n_3ad2ant1
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      (.classMem Q (syn_cnnc))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n)))
      p0163
  have p0165 :=
    @g_simp21
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (.cv u) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u)) (.classMem (syn_cpw (.cv g)) (.cv u)))
      (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n)))
  have p0166 :=
    @g_simp3l
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
  have p0167 := @g_nncaddccl (.cv u) (.cv n)
  have p0168 :=
    @g_syl2anc
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem (.cv u) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv u) (.cv n)) (syn_cnnc)) p0165 p0166 p0167
  have p0169 := @g_nndisjeq Q (syn_cplc (.cv u) (.cv n))
  have p0170 :=
    @g_syl2anc
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem Q (syn_cnnc)) (.classMem (syn_cplc (.cv u) (.cv n)) (syn_cnnc))
      (syn_wo (.classEq (syn_cin Q (syn_cplc (.cv u) (.cv n))) (syn_c0))
        (.classEq Q (syn_cplc (.cv u) (.cv n))))
      p0164 p0168 p0169
  have p0171 :=
    @g_orel1 (.classEq (syn_cin Q (syn_cplc (.cv u) (.cv n))) (syn_c0))
      (.classEq Q (syn_cplc (.cv u) (.cv n)))
  have p0172 :=
    @g_sylc
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.neg (.classEq (syn_cin Q (syn_cplc (.cv u) (.cv n))) (syn_c0)))
      (syn_wo (.classEq (syn_cin Q (syn_cplc (.cv u) (.cv n))) (syn_c0))
        (.classEq Q (syn_cplc (.cv u) (.cv n))))
      (.classEq Q (syn_cplc (.cv u) (.cv n))) p0162 p0170 p0171
  have p0173 := @g_ne0i (.cv u) (syn_cpw (.cv g))
  have p0174 :=
    @g_syl
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem (syn_cpw (.cv g)) (.cv u)) (syn_wne (.cv u) (syn_c0)) p0152 p0173
  have p0175 := (Nominal.biimpRefl (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
  have p0176 := @g_ssdif0 (syn_cpw (.cv b)) (syn_cpw (.cv g))
  have p0177 := @g_eqss (syn_cpw (.cv g)) (syn_cpw (.cv b))
  have p0178 :=
    @g_simplbi2 (.classEq (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wss (syn_cpw (.cv b)) (syn_cpw (.cv g))) p0177
  have p0179 :=
    @g_syl5bir (.classEq (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0))
      (syn_wss (syn_cpw (.cv b)) (syn_cpw (.cv g)))
      (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (.classEq (syn_cpw (.cv g)) (syn_cpw (.cv b))) p0176 p0178
  have p0180 :=
    @g_necon3d (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0) (syn_cpw (.cv g))
      (syn_cpw (.cv b)) p0179
  have p0181 :=
    @g_imp (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wne (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wne (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0)) p0180
  have p0182 :=
    @g_sylbi (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wa (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
        (syn_wne (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      (syn_wne (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0)) p0175 p0181
  have p0183 :=
    @g_syl
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wne (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0)) p0147 p0182
  have p0184 := @g_eleq2 (.cv n) (syn_c0c) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g)))
  have p0185 :=
    @g_biimpcd (.classEq (.cv n) (syn_c0c))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0c)) p0184
  have p0186 := @g_el0c (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g)))
  have p0187 :=
    @g_syl6ib (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
      (.classEq (.cv n) (syn_c0c))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0c))
      (.classEq (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0)) p0185 p0186
  have p0188 :=
    @g_necon3ad (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
      (.classEq (.cv n) (syn_c0c)) (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0)
      p0187
  have p0189 :=
    @g_sylc
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
      (syn_wne (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_c0))
      (.neg (.classEq (.cv n) (syn_c0c))) p0153 p0183 p0188
  have p0190 := @g_nnc0suc m (.cv n) dv_cache_0031
  have p0191 :=
    @g_sylib
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wo (.classEq (.cv n) (syn_c0c))
        (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))))
      p0166 p0190
  have p0192 :=
    @g_orel1 (.classEq (.cv n) (syn_c0c))
      (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))))
  have p0193 :=
    @g_sylc
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.neg (.classEq (.cv n) (syn_c0c)))
      (syn_wo (.classEq (.cv n) (syn_c0c))
        (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))))
      (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))) p0189 p0191
      p0192
  have p0194 := @g_addceq2 (.cv n) (syn_cplc (.cv m) (syn_c1c)) (.cv u)
  have p0195 := @g_addcass (.cv u) (.cv m) (syn_c1c)
  have p0196 :=
    @g_syl6eqr (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (.cv u) (.cv n))
      (syn_cplc (.cv u) (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (syn_cplc (.cv u) (.cv m)) (syn_c1c)) p0194 p0195
  have p0197 :=
    @g_reximi (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
      (.classEq (syn_cplc (.cv u) (.cv n)) (syn_cplc (syn_cplc (.cv u) (.cv m)) (syn_c1c)))
      m (syn_cnnc) p0196
  have p0198 :=
    @g_syl
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc (.cv u) (.cv n))
          (syn_cplc (syn_cplc (.cv u) (.cv m)) (syn_c1c))))
      p0193 p0197
  have p0199 := @g_vex u
  have p0200 := @g_vex n
  have p0201 := @g_addcex (.cv u) (.cv n) p0199 p0200
  have p0202 :=
    @g_opkltfing m (.cv u) (syn_cplc (.cv u) (.cv n)) (syn_cvv) (syn_cvv) dv_cache_0032
      dv_cache_0033
  have p0203 :=
    @g_mp2an (.classMem (.cv u) (syn_cvv))
      (.classMem (syn_cplc (.cv u) (.cv n)) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv u) (syn_cplc (.cv u) (.cv n))) (syn_cltfin))
        (syn_wa (syn_wne (.cv u) (syn_c0)) (syn_wrex m (syn_cnnc)
            (.classEq (syn_cplc (.cv u) (.cv n))
              (syn_cplc (syn_cplc (.cv u) (.cv m)) (syn_c1c))))))
      p0199 p0201 p0202
  have p0204 :=
    @g_sylanbrc
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (syn_wne (.cv u) (syn_c0))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc (.cv u) (.cv n))
          (syn_cplc (syn_cplc (.cv u) (.cv m)) (syn_c1c))))
      (.classMem (syn_copk (.cv u) (syn_cplc (.cv u) (.cv n))) (syn_cltfin)) p0174 p0198
      p0203
  have p0205 := @g_opkeq2 Q (syn_cplc (.cv u) (.cv n)) (.cv u)
  have p0206 :=
    @g_eleq1d (.classEq Q (syn_cplc (.cv u) (.cv n))) (syn_copk (.cv u) Q)
      (syn_copk (.cv u) (syn_cplc (.cv u) (.cv n))) (syn_cltfin) p0205
  have p0207 :=
    @g_syl5ibrcom
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classMem (syn_copk (.cv u) Q) (syn_cltfin))
      (.classEq Q (syn_cplc (.cv u) (.cv n)))
      (.classMem (syn_copk (.cv u) (syn_cplc (.cv u) (.cv n))) (syn_cltfin)) p0204 p0206
  have p0208 :=
    @g_mpd
      (syn_w3a (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))) (syn_wa (.classMem (.cv n) (syn_cnnc))
          (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))))
      (.classEq Q (syn_cplc (.cv u) (.cv n)))
      (.classMem (syn_copk (.cv u) Q) (syn_cltfin)) p0172 p0207
  have p0209 :=
    @g_n_3expa
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))) (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b))))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n)))
      (.classMem (syn_copk (.cv u) Q) (syn_cltfin)) p0208
  have p0210 :=
    @g_exp32
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
      (.classMem (syn_copk (.cv u) Q) (syn_cltfin)) p0209
  have p0211 :=
    @g_rexlimdv
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n))
      (.classMem (syn_copk (.cv u) Q) (syn_cltfin)) n (syn_cnnc) dv_cache_0034
      dv_cache_0035 p0210
  have p0212 :=
    @g_syl5bi (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cfin))
      (syn_wrex n (syn_cnnc) (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (.cv n)))
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (syn_copk (.cv u) Q) (syn_cltfin)) p0141 p0211
  have p0213 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (syn_cdif (syn_cpw (.cv b)) (syn_cpw (.cv g))) (syn_cfin))
      (.classMem (syn_copk (.cv u) Q) (syn_cltfin)) p0140 p0212
  have p0214 := @g_opkeq1 (.cv u) N Q
  have p0215 :=
    @g_eleq1d (.classEq (.cv u) N) (syn_copk (.cv u) Q) (syn_copk N Q) (syn_cltfin) p0214
  have p0216 :=
    @g_syl5ibcom
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classMem (syn_copk (.cv u) Q) (syn_cltfin)) (.classEq (.cv u) N)
      (.classMem (syn_copk N Q) (syn_cltfin)) p0213 p0215
  have p0217 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a
            (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
              (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
                (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
                (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
            (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
              (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
              (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
          (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
            (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
        (syn_w3a (.classMem (.cv u) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
            (.classMem (syn_cpw (.cv g)) (.cv u)))
          (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))))
      (.classEq (.cv u) N) (.classMem (syn_copk N Q) (syn_cltfin)) p0122 p0216
  have p0218 :=
    @g_n_3exp2
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (.cv u) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u)) (.classMem (syn_cpw (.cv g)) (.cv u)))
      (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0217
  have p0219 :=
    @g_rexlimdv
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u)) (.classMem (syn_cpw (.cv g)) (.cv u)))
      (.imp (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
        (.classMem (syn_copk N Q) (syn_cltfin)))
      u (syn_cnnc) dv_cache_0036 dv_cache_0037 p0218
  have p0220 :=
    @g_mpd
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_wrex u (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv u))
          (.classMem (syn_cpw (.cv g)) (.cv u))))
      (.imp (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
        (.classMem (syn_copk N Q) (syn_cltfin)))
      p0107 p0219
  have p0221 :=
    @g_syl5
      (syn_wa (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
        (syn_wa (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b)))
          (.neg (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g))))))
      (syn_wpss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0100 p0220
  have p0222 :=
    @g_mpand
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_wss (syn_cpw (.cv g)) (syn_cpw (.cv b)))
      (syn_wa (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b)))
        (.neg (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g)))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0093 p0221
  have p0223 :=
    @g_syl5bir (syn_wa (.objMem x b) (.neg (.objMem x g)))
      (syn_wa (.classMem (syn_csn (.cv x)) (syn_cpw (.cv b)))
        (.neg (.classMem (syn_csn (.cv x)) (syn_cpw (.cv g)))))
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0086 p0222
  have p0224 :=
    @g_syld
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.objMem x d) (syn_wa (.objMem x b) (.neg (.objMem x g)))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0081 p0223
  have p0225 :=
    @g_exlimdv
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.objMem x d) (.classMem (syn_copk N Q) (syn_cltfin)) x dv_cache_0038 dv_cache_0039
      p0224
  have p0226_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wne (.cv d) (syn_c0)) (syn_wex x (.objMem x d))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv syn_wex
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
    @g_syl5bi (syn_wne (.cv d) (syn_c0)) (syn_wex x (.objMem x d))
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0226_e00_recanon p0225
  have p0227 :=
    @g_mpd
      (syn_wa (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
        (syn_wa (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_wne (.cv d) (syn_c0)) (.classMem (syn_copk N Q) (syn_cltfin)) p0070 p0226
  have p0228 :=
    @g_exp32
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (syn_wa (.objMem g r) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
      (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
        (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0227
  have p0229_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
          (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
            (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
            (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))) (.imp
          (syn_wa (.classMem (.cv g) (.cv r)) (.classMem (.cv d) (syn_cplc (.cv t) (syn_c1c))))
          (.imp (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
              (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))
            (.classMem (syn_copk N Q) (syn_cltfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl
          syn_csn syn_cltfin syn_wex
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
    @g_rexlimdvv
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
        (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))
      (.classMem (syn_copk N Q) (syn_cltfin)) g d (.cv r) (syn_cplc (.cv t) (syn_c1c))
      dv_cache_0021 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0024
      p0229_e00_recanon
  have p0230 :=
    @g_syl5bi (.classMem (.cv b) (syn_cplc (.cv r) (syn_cplc (.cv t) (syn_c1c))))
      (syn_wrex g (.cv r) (syn_wrex d (syn_cplc (.cv t) (syn_c1c))
          (syn_wa (.classEq (syn_cin (.cv g) (.cv d)) (syn_c0))
            (.classEq (.cv b) (syn_cun (.cv g) (.cv d))))))
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0063 p0229
  have p0231 :=
    @g_mpd
      (syn_w3a (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))) (syn_wa (.classMem (.cv t) (syn_cnnc))
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem (.cv b) (syn_cplc (.cv r) (syn_cplc (.cv t) (syn_c1c))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0062 p0230
  have p0232 :=
    @g_n_3expa
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
        (syn_wa (.objMem a r) (.objMem b s)))
      (syn_wa (.classMem (.cv t) (syn_cnnc))
        (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0231
  have p0233 :=
    @g_exp32
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (.cv t) (syn_cnnc))
      (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0232
  have p0234 :=
    @g_rexlimdv
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))
      (.classMem (syn_copk N Q) (syn_cltfin)) t (syn_cnnc) dv_cache_0044 dv_cache_0045
      p0233
  have p0235 :=
    @g_adantld
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (syn_wrex t (syn_cnnc) (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c))))
      (.classMem (syn_copk N Q) (syn_cltfin)) (syn_wne (.cv r) (syn_c0)) p0234
  have p0236 :=
    @g_sylbid
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (syn_copk (.cv r) (.cv s)) (syn_cltfin))
      (syn_wa (syn_wne (.cv r) (syn_c0)) (syn_wrex t (syn_cnnc)
          (.classEq (.cv s) (syn_cplc (syn_cplc (.cv r) (.cv t)) (syn_c1c)))))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0057 p0235
  have p0237 :=
    @g_sylbird
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classMem (syn_copk (syn_ctfin (.cv r)) (syn_ctfin (.cv s))) (syn_cltfin))
      (.classMem (syn_copk (.cv r) (.cv s)) (syn_cltfin))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0055 p0236
  have p0238 := @g_opkeq12 M P (syn_ctfin (.cv r)) (syn_ctfin (.cv s))
  have p0239 :=
    @g_eleq1d (syn_wa (.classEq M (syn_ctfin (.cv r))) (.classEq P (syn_ctfin (.cv s))))
      (syn_copk M P) (syn_copk (syn_ctfin (.cv r)) (syn_ctfin (.cv s))) (syn_cltfin) p0238
  have p0240 :=
    @g_imbi1d (syn_wa (.classEq M (syn_ctfin (.cv r))) (.classEq P (syn_ctfin (.cv s))))
      (.classMem (syn_copk M P) (syn_cltfin))
      (.classMem (syn_copk (syn_ctfin (.cv r)) (syn_ctfin (.cv s))) (syn_cltfin))
      (.classMem (syn_copk N Q) (syn_cltfin)) p0239
  have p0241 :=
    @g_syl5ibrcom
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      (syn_wa (.classEq M (syn_ctfin (.cv r))) (.classEq P (syn_ctfin (.cv s))))
      (.imp (.classMem (syn_copk (syn_ctfin (.cv r)) (syn_ctfin (.cv s))) (syn_cltfin))
        (.classMem (syn_copk N Q) (syn_cltfin)))
      p0237 p0240
  have p0242 :=
    @g_mp2and
      (syn_wa (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
        (syn_wa (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
          (syn_wa (.objMem a r) (.objMem b s))))
      (.classEq M (syn_ctfin (.cv r))) (.classEq P (syn_ctfin (.cv s)))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0034 p0053 p0241
  have p0243 :=
    @g_exp32
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
      (syn_wa (.objMem a r) (.objMem b s))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0242
  have p0244 :=
    @g_syl7
      (syn_wa (syn_wa (.objMem a r) (.objMem a r)) (syn_wa (.objMem b s) (.objMem b s)))
      (syn_wa (.objMem a r) (.objMem b s))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classMem (.cv s) (syn_cnnc)))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0015 p0243
  have p0245 :=
    @g_rexlimdvv
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wa (syn_wa (.objMem a r) (.objMem a r)) (syn_wa (.objMem b s) (.objMem b s)))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      r s (syn_cnnc) (syn_cnnc) dv_cache_0009 dv_cache_0046 dv_cache_0047 dv_cache_0048
      dv_cache_0049 dv_cache_0013 p0244
  have p0246 :=
    @g_syl5bir
      (syn_wa (syn_wrex r (syn_cnnc) (syn_wa (.objMem a r) (.objMem a r)))
        (syn_wrex s (syn_cnnc) (syn_wa (.objMem b s) (.objMem b s))))
      (syn_wrex r (syn_cnnc) (syn_wrex s (syn_cnnc) (syn_wa (syn_wa (.objMem a r) (.objMem a r))
            (syn_wa (.objMem b s) (.objMem b s)))))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0012 p0245
  have p0247 :=
    @g_mp2and
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wrex r (syn_cnnc) (syn_wa (.objMem a r) (.objMem a r)))
      (syn_wrex s (syn_cnnc) (syn_wa (.objMem b s) (.objMem b s)))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0007 p0011 p0246
  have p0248 :=
    @g_n_3expia (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0247
  have p0249 :=
    @g_exlimdvv
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      a b dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 p0248
  have p0250 :=
    @g_syl5bir
      (syn_wa (syn_wex a
          (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))) (syn_wex b
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (syn_wex a (syn_wex b (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0003 p0249
  have p0251 :=
    @g_n_3impia (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc)))
      (syn_wa (syn_wex a
          (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))) (syn_wex b
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0250
  have p0252 :=
    @g_sylbir
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex a
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))))
        (syn_w3a (.classMem P (syn_cnnc)) (.classMem Q (syn_cnnc)) (syn_wex b
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem Q (syn_cnnc))) (syn_wa (syn_wex a
            (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N)))
          (syn_wex b
            (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q)))))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      p0002 p0251
  have p0253 :=
    @g_syl2anb (syn_wsfin M N)
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex a
          (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))))
      (syn_w3a (.classMem P (syn_cnnc)) (.classMem Q (syn_cnnc)) (syn_wex b
          (syn_wa (.classMem (syn_cpw1 (.cv b)) P) (.classMem (syn_cpw (.cv b)) Q))))
      (.imp (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin)))
      (syn_wsfin P Q) p0000 p0001 p0252
  have p0254 :=
    @g_imp (syn_wa (syn_wsfin M N) (syn_wsfin P Q))
      (.classMem (syn_copk M P) (syn_cltfin)) (.classMem (syn_copk N Q) (syn_cltfin))
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

@[expose]
noncomputable def g_sfin111 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.classEq M N)) :=
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
  have dv_cache_0004 : a ∉ ((syn_wne M (syn_c0))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin N P a
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_simp2bi (syn_wsfin N P) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) N) (.classMem (syn_cpw (.cv a)) P)))
      p0000
  have p0002 := @g_adantl (syn_wsfin N P) (.classMem P (syn_cnnc)) (syn_wsfin M P) p0001
  have p0003 := @g_ltfinirr P
  have p0004 :=
    @g_syl (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.classMem P (syn_cnnc))
      (.neg (.classMem (syn_copk P P) (syn_cltfin))) p0002 p0003
  have p0005 := @g_sfinltfin N P M P
  have p0006 :=
    @g_mtand (syn_wa (syn_wsfin M P) (syn_wsfin N P))
      (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk P P) (syn_cltfin))
      p0004 p0005
  have p0007 := @g_sfinltfin M P N P
  have p0008 :=
    @g_ex (syn_wa (syn_wsfin N P) (syn_wsfin M P)) (.classMem (syn_copk N M) (syn_cltfin))
      (.classMem (syn_copk P P) (syn_cltfin)) p0007
  have p0009 :=
    @g_ancoms (syn_wsfin N P) (syn_wsfin M P)
      (.imp (.classMem (syn_copk N M) (syn_cltfin)) (.classMem (syn_copk P P) (syn_cltfin)))
      p0008
  have p0010 :=
    @g_mtod (syn_wa (syn_wsfin M P) (syn_wsfin N P))
      (.classMem (syn_copk N M) (syn_cltfin)) (.classMem (syn_copk P P) (syn_cltfin))
      p0004 p0009
  have p0011 :=
    @g_ioran (.classMem (syn_copk M N) (syn_cltfin))
      (.classMem (syn_copk N M) (syn_cltfin))
  have p0012 :=
    @g_sylanbrc (syn_wa (syn_wsfin M P) (syn_wsfin N P))
      (.neg (.classMem (syn_copk M N) (syn_cltfin)))
      (.neg (.classMem (syn_copk N M) (syn_cltfin)))
      (.neg (syn_wo (.classMem (syn_copk M N) (syn_cltfin))
          (.classMem (syn_copk N M) (syn_cltfin))))
      p0006 p0010 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M P a
      dv_cache_0003 dv_cache_0002
  have p0014 :=
    @g_simp1bi (syn_wsfin M P) (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) P)))
      p0013
  have p0015 := @g_adantr (syn_wsfin M P) (.classMem M (syn_cnnc)) (syn_wsfin N P) p0014
  have p0016 :=
    @g_simp1bi (syn_wsfin N P) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) N) (.classMem (syn_cpw (.cv a)) P)))
      p0000
  have p0017 := @g_adantl (syn_wsfin N P) (.classMem N (syn_cnnc)) (syn_wsfin M P) p0016
  have p0018 := @g_ne0i M (syn_cpw1 (.cv a))
  have p0019 :=
    @g_adantr (.classMem (syn_cpw1 (.cv a)) M) (syn_wne M (syn_c0))
      (.classMem (syn_cpw (.cv a)) P) p0018
  have p0020 :=
    @g_exlimiv (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) P))
      (syn_wne M (syn_c0)) a dv_cache_0004 p0019
  have p0021 :=
    @g_n_3ad2ant3
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) P)))
      (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (.classMem P (syn_cnnc)) p0020
  have p0022 :=
    @g_sylbi (syn_wsfin M P)
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex a
          (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) P))))
      (syn_wne M (syn_c0)) p0013 p0021
  have p0023 := @g_adantr (syn_wsfin M P) (syn_wne M (syn_c0)) (syn_wsfin N P) p0022
  have p0024 := @g_ltfintri M N
  have p0025 :=
    @g_syl3anc (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.classMem M (syn_cnnc))
      (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
        (.classMem (syn_copk N M) (syn_cltfin)))
      p0015 p0017 p0023 p0024
  have p0026 :=
    (Nominal.biimpRefl (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
        (.classMem (syn_copk N M) (syn_cltfin))))
  have p0027 :=
    @g_sylib (syn_wa (syn_wsfin M P) (syn_wsfin N P))
      (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
        (.classMem (syn_copk N M) (syn_cltfin)))
      (syn_wo (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N))
        (.classMem (syn_copk N M) (syn_cltfin)))
      p0025 p0026
  have p0028 :=
    @g_or32 (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
      (.classMem (syn_copk N M) (syn_cltfin))
  have p0029 :=
    @g_sylib (syn_wa (syn_wsfin M P) (syn_wsfin N P))
      (syn_wo (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N))
        (.classMem (syn_copk N M) (syn_cltfin)))
      (syn_wo (syn_wo (.classMem (syn_copk M N) (syn_cltfin))
          (.classMem (syn_copk N M) (syn_cltfin))) (.classEq M N))
      p0027 p0028
  have p0030 :=
    @g_orel1
      (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)))
      (.classEq M N)
  have p0031 :=
    @g_sylc (syn_wa (syn_wsfin M P) (syn_wsfin N P))
      (.neg (syn_wo (.classMem (syn_copk M N) (syn_cltfin))
          (.classMem (syn_copk N M) (syn_cltfin))))
      (syn_wo (syn_wo (.classMem (syn_copk M N) (syn_cltfin))
          (.classMem (syn_copk N M) (syn_cltfin))) (.classEq M N))
      (.classEq M N) p0012 p0029 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end
