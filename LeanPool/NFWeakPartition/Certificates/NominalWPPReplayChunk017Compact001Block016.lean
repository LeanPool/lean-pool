/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk017Compact001Part067

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part068`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as
`g_wppstopgammacontrgrowthstagedndv`.
-/
@[expose]
noncomputable def gWppstopgammacontrgrowthstagedndv (x : Var) (y : Var) (C : Class)
    (F : Class) (p : Var) (dv_C_p : p ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_F_p : p ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_p_x : p ≠ x)
    (dv_p_y : p ≠ y) (dv_x_y : x ≠ y)
    (hyp_wppstopgammacontrgrowthstagedndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopgammacontrgrowthstagedndv_2 :
      Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv))))
    (hyp_wppstopgammacontrgrowthstagedndv_3 :
      Nominal.NPrf (.classMem C (synChwcards (synCvv))))
    (hyp_wppstopgammacontrgrowthstagedndv_4 : Nominal.NPrf (synWbr (synCtc C) (synClec) C))
    (hyp_wppstopgammacontrgrowthstagedndv_5 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F)))))
    (hyp_wppstopgammacontrgrowthstagedndv_6 : Nominal.NPrf
        (synWral x (synCdm (synCwppstopstep F C))
          (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x)))
            (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))))))
    (hyp_wppstopgammacontrgrowthstagedndv_7 : Nominal.NPrf (synWral y (synChwcards (synCvv))
          (.imp (synWbr C (synClec) (.cv y)) (synWne (.cv y) (synCtc (.cv y)))))) :
    Nominal.NPrf
      (.imp (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
        (.neg (.classEq (synC0c) (synC0c)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ C.fv ∪ F.fv ∪ ({ p } : Finset Var)
  let m : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let k : Var := freshVar proofSupport 2
  let n : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  let r : Var := freshVar proofSupport 5
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_ne_x : m ≠ x := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_m : x ≠ m := Ne.symm fresh_m_ne_x
  have fresh_m_ne_y : m ≠ y := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_m : y ≠ m := Ne.symm fresh_m_ne_y
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_ne_p : m ≠ p := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_m : p ≠ m := Ne.symm fresh_m_ne_p
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_p : z ≠ p := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_z : p ≠ z := Ne.symm fresh_z_ne_p
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_k_ne_x : k ≠ x := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_k : x ≠ k := Ne.symm fresh_k_ne_x
  have fresh_k_ne_y : k ≠ y := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_k : y ≠ k := Ne.symm fresh_k_ne_y
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_ne_p : k ≠ p := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_k : p ≠ k := Ne.symm fresh_k_ne_p
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_y : n ≠ y := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_p : n ≠ p := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_p : r ≠ p := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_r : p ≠ r := Ne.symm fresh_r_ne_p
  have fresh_m_ne_z : m ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_m : z ≠ m := Ne.symm fresh_m_ne_z
  have fresh_m_ne_k : m ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have fresh_m_ne_n : m ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_n_ne_m : n ≠ m := Ne.symm fresh_m_ne_n
  have fresh_m_ne_q : m ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_k : z ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_k_ne_z : k ≠ z := Ne.symm fresh_z_ne_k
  have fresh_z_ne_n : z ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_n_ne_z : n ≠ z := Ne.symm fresh_z_ne_n
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
  have fresh_k_ne_n : k ≠ n :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_n_ne_k : n ≠ k := Ne.symm fresh_k_ne_n
  have fresh_k_ne_q : k ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_k : q ≠ k := Ne.symm fresh_k_ne_q
  have fresh_n_ne_q : n ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_n_ne_r : n ≠ r :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have dv_cache_0001 : k ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_C, not_false_eq_true])
  have dv_cache_0002 : m ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_C, not_false_eq_true])
  have dv_cache_0003 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_C, not_false_eq_true])
  have dv_cache_0004 : q ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0006 : k ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_F, not_false_eq_true])
  have dv_cache_0007 : m ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_F, not_false_eq_true])
  have dv_cache_0008 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_F, not_false_eq_true])
  have dv_cache_0009 : q ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_F, not_false_eq_true])
  have dv_cache_0010 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0011 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show k ≠ m from (by exact fresh_k_ne_m))
  have dv_cache_0012 : k ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show k ≠ n from (by exact fresh_k_ne_n))
  have dv_cache_0013 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show k ≠ q from (by exact fresh_k_ne_q))
  have dv_cache_0014 : k ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show k ≠ x from (by exact fresh_k_ne_x))
  have dv_cache_0015 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0016 : m ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show m ≠ q from (by exact fresh_m_ne_q))
  have dv_cache_0017 : m ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0018 : n ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show n ≠ q from (by exact fresh_n_ne_q))
  have dv_cache_0019 : n ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0020 : q ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have dv_cache_0021 : n ∉ ((synCnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0022 : z ∉ ((synCnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0023 :
    z ∉
      ((Wff.imp (.classMem (.cv n)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_n, fresh_z_not_C, fresh_z_not_F, fresh_z_ne_m,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 :
    n ∉
      ((Wff.imp (.classMem (.cv z)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_z, fresh_n_not_C, fresh_n_not_F, fresh_n_ne_m,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0025 : q ∉ ((synCnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0026 :
    z ∉
      ((Wff.imp (.classMem (.cv q) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_q, fresh_z_not_C, fresh_z_not_F, fresh_z_ne_k,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 :
    q ∉
      ((Wff.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_z, fresh_q_not_C, fresh_q_not_F, fresh_q_ne_k,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0028 : k ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0029 : m ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0030 :
    k ∉
      ((synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_m, fresh_k_not_C,
          fresh_k_not_F, fresh_k_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0031 :
    m ∉
      ((synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_ne_k, fresh_m_not_C,
          fresh_m_not_F, fresh_m_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0032 : m ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show m ≠ k from (by exact fresh_m_ne_k))
  have dv_cache_0033 : y ∉ ((synCdm (synCwppstopstep F C))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_y, dv_F_y, or_false, not_false_eq_true])
  have dv_cache_0034 : r ∉ ((synCdm (synCwppstopstep F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_r_not_C, fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0035 :
    r ∉
      ((Wff.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, Finset.mem_singleton, fresh_r_not_C, fresh_r_ne_y,
          fresh_r_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0036 :
    y ∉
      ((Wff.imp (synWbr (synCtc C) (synClec) (.cv r))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, Finset.mem_singleton, dv_C_y, fresh_y_ne_r, dv_F_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0037 : p ∉ (C).fv :=
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
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0038 : y ∉ (C).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0039 : p ∉ (F).fv :=
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
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0040 : y ∉ (F).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0041 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0042 : p ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (show p ≠ y from (by exact dv_p_y))
  have dv_cache_0043 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0044 :
    z ∉
      ((Wff.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))).fv :=
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
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_n, fresh_z_not_C, fresh_z_not_F, fresh_z_ne_k,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0045 :
    n ∉
      ((Wff.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_z, fresh_n_not_C, fresh_n_not_F, fresh_n_ne_k,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0046 : k ∉ ((synCwppgamma (synCwppstopstep F C) C)).fv :=
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
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_k_not_C, fresh_k_not_F, or_false, not_false_eq_true])
  have dv_cache_0047 : m ∉ ((synCwppgamma (synCwppstopstep F C) C)).fv :=
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
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_m_not_C, fresh_m_not_F, or_false, not_false_eq_true])
  have dv_cache_0048 : n ∉ ((synCwppgamma (synCwppstopstep F C) C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_n_not_C, fresh_n_not_F, or_false, not_false_eq_true])
  have dv_cache_0049 : p ∉ ((synCwppgamma (synCwppstopstep F C) C)).fv :=
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
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_p, dv_F_p, or_false, not_false_eq_true])
  have dv_cache_0050 : x ∉ ((synCwppgamma (synCwppstopstep F C) C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_x, dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0051 : y ∉ ((synCwppgamma (synCwppstopstep F C) C)).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_y, dv_F_y, or_false, not_false_eq_true])
  have dv_cache_0052 :
    n ∉
      ((synWral r (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv r))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F,
          fresh_n_ne_r, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0053 :
    p ∉
      ((synWral r (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv r))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))).fv :=
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
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_p, dv_F_p, fresh_p_ne_r,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0054 :
    x ∉
      ((synWral r (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv r))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))).fv :=
    by
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_x, dv_F_x, fresh_x_ne_r,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0055 :
    y ∉
      ((synWral r (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv r))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))).fv :=
    by
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_y, dv_F_y, fresh_y_ne_r,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0056 : k ≠ p :=
    by
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
    exact (show k ≠ p from (by exact fresh_k_ne_p))
  have dv_cache_0057 : k ≠ y :=
    by
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
    exact (show k ≠ y from (by exact fresh_k_ne_y))
  have dv_cache_0058 : m ≠ p :=
    by
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
    exact (show m ≠ p from (by exact fresh_m_ne_p))
  have dv_cache_0059 : m ≠ y :=
    by
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
    exact (show m ≠ y from (by exact fresh_m_ne_y))
  have dv_cache_0060 : n ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact (show n ≠ p from (by exact fresh_n_ne_p))
  have dv_cache_0061 :
    n ∉
      ((synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_C,
          fresh_n_not_F, fresh_n_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0062 :
    n ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_k, fresh_n_not_C,
          fresh_n_not_F, fresh_n_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0063 : n ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
    exact (show n ≠ y from (by exact fresh_n_ne_y))
  have dv_cache_0064 :
    p ∉
      ((synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_ne_m, dv_C_p, dv_F_p,
          fresh_p_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0065 :
    p ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_ne_k, dv_C_p, dv_F_p,
          fresh_p_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0066 :
    x ∉
      ((synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_m, dv_C_x, dv_F_x,
          fresh_x_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0067 :
    y ∉
      ((synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_m, dv_C_y, dv_F_y,
          fresh_y_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0068 :
    x ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_k, dv_C_x, dv_F_x,
          fresh_x_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0069 :
    y ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_k, dv_C_y, dv_F_y,
          fresh_y_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0070 :
    m ∉
      ((Wff.imp (synWral y (synCdm (synCwppstopstep F C))
            (.imp (synWbr (synCtc C) (synClec) (.cv y))
              (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
          (.neg (.classEq (synC0c) (synC0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_not_C, fresh_m_not_F,
          fresh_m_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0071 :
    k ∉
      ((Wff.imp (synWral y (synCdm (synCwppstopstep F C))
            (.imp (synWbr (synCtc C) (synClec) (.cv y))
              (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
          (.neg (.classEq (synC0c) (synC0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F,
          fresh_k_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gWppstopgammaleasthitpairndv x C k m n F q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      hyp_wppstopgammacontrgrowthstagedndv_1 hyp_wppstopgammacontrgrowthstagedndv_2
      hyp_wppstopgammacontrgrowthstagedndv_3 hyp_wppstopgammacontrgrowthstagedndv_6
  have p0001 := @gId (.classEq (.cv n) (.cv z))
  have p0002 :=
    @gEleq1d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z)
      (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C)
      p0001
  have p0003 := @gId (.classEq (.cv n) (.cv z))
  have p0004 :=
    @gBreq2d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z) (.cv m) (synCkqrel (synClefin))
      p0003
  have p0005 :=
    @gImbi12d (.classEq (.cv n) (.cv z))
      (.classMem (.cv n)
        (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
      (.classMem (.cv z)
        (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)) p0002 p0004
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n z) (synWb (.imp (.classMem (.cv n)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpphit synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCcnv synCopab synCfrec synCclos1 synCint
          synCsn synCpprod synCtxp synCin synCcom synCmpt synCvv synCplc synC1c
          synCwppstopstep synCwppgamma synCio synCuni
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gCbvralv
      (.imp (.classMem (.cv n)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))
      (.imp (.classMem (.cv z)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))
      n z (synCnnc) dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      p0006_e00_recanon
  have p0007 :=
    @gAnbi2i
      (synWral n (synCnnc) (.imp (.classMem (.cv n)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))
      (synWral z (synCnnc) (.imp (.classMem (.cv z)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv m)
        (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
      p0006
  have p0008 :=
    @gRexbii
      (synWa (.classMem (.cv m)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWral n (synCnnc) (.imp (.classMem (.cv n)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))))
      (synWa (.classMem (.cv m)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))
      m (synCnnc) p0007
  have p0009 := @gId (.classEq (.cv q) (.cv z))
  have p0010 :=
    @gEleq1d (.classEq (.cv q) (.cv z)) (.cv q) (.cv z)
      (synCwpphit (synCwppstopstep F (synCtc C))
        (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C))
      p0009
  have p0011 := @gId (.classEq (.cv q) (.cv z))
  have p0012 :=
    @gBreq2d (.classEq (.cv q) (.cv z)) (.cv q) (.cv z) (.cv k) (synCkqrel (synClefin))
      p0011
  have p0013 :=
    @gImbi12d (.classEq (.cv q) (.cv z))
      (.classMem (.cv q) (synCwpphit (synCwppstopstep F (synCtc C))
          (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
      (.classMem (.cv z) (synCwpphit (synCwppstopstep F (synCtc C))
          (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)) p0010 p0012
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq q z) (synWb (.imp (.classMem (.cv q)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpphit synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCcnv synCopab synCfrec synCclos1 synCint
          synCsn synCpprod synCtxp synCin synCcom synCmpt synCvv synCplc synC1c
          synCwppstopstep synCtc synCio synCuni
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @gCbvralv
      (.imp (.classMem (.cv q) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))
      (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))
      q z (synCnnc) dv_cache_0025 dv_cache_0022 dv_cache_0026 dv_cache_0027
      p0014_e00_recanon
  have p0015 :=
    @gAnbi2i
      (synWral q (synCnnc) (.imp (.classMem (.cv q)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))
      (synWral z (synCnnc) (.imp (.classMem (.cv z)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
          (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
      p0014
  have p0016 :=
    @gRexbii
      (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWral q (synCnnc) (.imp (.classMem (.cv q)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
      (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))
      k (synCnnc) p0015
  have p0017 :=
    @gAnbi12i
      (synWrex m (synCnnc) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))))
      (synWrex m (synCnnc) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
      (synWrex k (synCnnc) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral q (synCnnc) (.imp (.classMem (.cv q)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWrex k (synCnnc) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      p0008 p0016
  have p0018 :=
    @gMpbi
      (synWa (synWrex m (synCnnc) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))))) (synWrex k (synCnnc)
          (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral q (synCnnc) (.imp (.classMem (.cv q)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))))
      (synWa (synWrex m (synCnnc) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))) (synWrex k (synCnnc)
          (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      p0000 p0017
  have p0019 :=
    @gReeanv
      (synWa (.classMem (.cv m)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))
      (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))
      m k (synCnnc) (synCnnc) dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
      dv_cache_0032
  have p0020 :=
    @gMpbir
      (synWrex m (synCnnc) (synWrex k (synCnnc) (synWa (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
              (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))))
      (synWa (synWrex m (synCnnc) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))) (synWrex k (synCnnc)
          (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      p0018 p0019
  have p0021 :=
    @gSimpl (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
  have p0022 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) (synWa
          (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
            (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)) p0021
  have p0023 :=
    @gSimpr (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
  have p0024 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) (synWa
          (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
            (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (synWa (.classMem (.cv m)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))
      (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))
      p0023
  have p0025 :=
    @gJca
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) (synWa
          (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
            (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (.classMem (.cv m) (synCnnc))
      (synWa (.classMem (.cv m)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))
      p0022 p0024
  have p0027 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) (synWa
          (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
            (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)) p0021
  have p0029 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) (synWa
          (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
            (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (synWa (.classMem (.cv m)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))
      (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))
      p0023
  have p0030 :=
    @gJca
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) (synWa
          (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
            (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (.classMem (.cv k) (synCnnc))
      (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))
      p0027 p0029
  have p0031 :=
    @gJca
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) (synWa
          (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
            (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      p0025 p0030
  have p0032 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
  have p0033 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
        (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))
      (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      p0032
  have p0035 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
        (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))
      (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      p0032
  have p0036 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
  have p0037 := @gId (.classEq (.cv y) (.cv r))
  have p0038 :=
    @gBreq2d (.classEq (.cv y) (.cv r)) (.cv y) (.cv r) (synCtc C) (synClec) p0037
  have p0039 := @gId (.classEq (.cv y) (.cv r))
  have p0040 :=
    @gFveq2d (.classEq (.cv y) (.cv r)) (.cv y) (.cv r) (synCwppstopstep F C) p0039
  have p0041 :=
    @gBreq2d (.classEq (.cv y) (.cv r)) (synCfv (synCwppstopstep F C) (.cv y))
      (synCfv (synCwppstopstep F C) (.cv r)) C (synClec) p0040
  have p0042 :=
    @gImbi12d (.classEq (.cv y) (.cv r)) (synWbr (synCtc C) (synClec) (.cv y))
      (synWbr (synCtc C) (synClec) (.cv r))
      (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))
      (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r))) p0038 p0041
  have p0043_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y r) (synWb (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))
          (.imp (synWbr (synCtc C) (synClec) (.cv r))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCtc synCio synCuni synCsn synClec synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0042
  have p0043 :=
    @gCbvralv
      (.imp (synWbr (synCtc C) (synClec) (.cv y))
        (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))
      (.imp (synWbr (synCtc C) (synClec) (.cv r))
        (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r))))
      y r (synCdm (synCwppstopstep F C)) dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 p0043_e00_recanon
  have p0044 :=
    @gBiimpi
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
      (synWral r (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv r))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))
      p0043
  have p0045 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
        (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
      (synWral r (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv r))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))
      p0036 p0044
  have p0046 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
        (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      (synWral r (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv r))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))
      p0035 p0045
  have p0047 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
        (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))
      (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
      (synWa (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
        (synWral r (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv r))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r))))))
      p0033 p0046
  have p0049 :=
    @gWppstopgammafixedhwdndv x y C F p dv_cache_0037 dv_cache_0005 dv_cache_0038
      dv_cache_0039 dv_cache_0010 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
      hyp_wppstopgammacontrgrowthstagedndv_1 hyp_wppstopgammacontrgrowthstagedndv_2
      hyp_wppstopgammacontrgrowthstagedndv_3 hyp_wppstopgammacontrgrowthstagedndv_4
      hyp_wppstopgammacontrgrowthstagedndv_5 hyp_wppstopgammacontrgrowthstagedndv_6
  have p0050 :=
    @gSimprd
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
      (.classMem (synCwppgamma (synCwppstopstep F C) C) (synChwcards (synCvv)))
      (.classEq (synCtc (synCwppgamma (synCwppstopstep F C) C))
        (synCwppgamma (synCwppstopstep F C) C))
      p0049
  have p0051 :=
    @gEqcomd
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
      (synCtc (synCwppgamma (synCwppstopstep F C) C))
      (synCwppgamma (synCwppstopstep F C) C) p0050
  have p0052 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
        (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
      (.classEq (synCwppgamma (synCwppstopstep F C) C)
        (synCtc (synCwppgamma (synCwppstopstep F C) C)))
      p0036 p0051
  have p0053 :=
    @gWppstopgammahwndv C F hyp_wppstopgammacontrgrowthstagedndv_1
      hyp_wppstopgammacontrgrowthstagedndv_2 hyp_wppstopgammacontrgrowthstagedndv_3
  have p0054 := @gId (.classEq (.cv n) (.cv z))
  have p0055 :=
    @gEleq1d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z)
      (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C)
      p0054
  have p0056 := @gId (.classEq (.cv n) (.cv z))
  have p0057 :=
    @gBreq2d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z) (.cv m) (synCkqrel (synClefin))
      p0056
  have p0058 :=
    @gImbi12d (.classEq (.cv n) (.cv z))
      (.classMem (.cv n)
        (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
      (.classMem (.cv z)
        (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)) p0055 p0057
  have p0059_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n z) (synWb (.imp (.classMem (.cv n)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpphit synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCcnv synCopab synCfrec synCclos1 synCint
          synCsn synCpprod synCtxp synCin synCcom synCmpt synCvv synCplc synC1c
          synCwppstopstep synCwppgamma synCio synCuni
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @gCbvralv
      (.imp (.classMem (.cv n)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))
      (.imp (.classMem (.cv z)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))
      n z (synCnnc) dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      p0059_e00_recanon
  have p0060 :=
    @gAnbi2i
      (synWral n (synCnnc) (.imp (.classMem (.cv n)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))
      (synWral z (synCnnc) (.imp (.classMem (.cv z)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv m)
        (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
      p0059
  have p0061 :=
    @gAnbi2i
      (synWa (.classMem (.cv m)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWral n (synCnnc) (.imp (.classMem (.cv n)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))))
      (synWa (.classMem (.cv m)
          (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))
      (.classMem (.cv m) (synCnnc)) p0060
  have p0062 :=
    @gBiimpri
      (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))))
      (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
      p0061
  have p0063 := @gId (.classEq (.cv n) (.cv z))
  have p0064 :=
    @gEleq1d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z)
      (synCwpphit (synCwppstopstep F (synCtc C))
        (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C))
      p0063
  have p0065 := @gId (.classEq (.cv n) (.cv z))
  have p0066 :=
    @gBreq2d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z) (.cv k) (synCkqrel (synClefin))
      p0065
  have p0067 :=
    @gImbi12d (.classEq (.cv n) (.cv z))
      (.classMem (.cv n) (synCwpphit (synCwppstopstep F (synCtc C))
          (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
      (.classMem (.cv z) (synCwpphit (synCwppstopstep F (synCtc C))
          (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)) p0064 p0066
  have p0068_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n z) (synWb (.imp (.classMem (.cv n)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpphit synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCcnv synCopab synCfrec synCclos1 synCint
          synCsn synCpprod synCtxp synCin synCcom synCmpt synCvv synCplc synC1c
          synCwppstopstep synCtc synCio synCuni
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0067
  have p0068 :=
    @gCbvralv
      (.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
      (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))
      n z (synCnnc) dv_cache_0021 dv_cache_0022 dv_cache_0044 dv_cache_0045
      p0068_e00_recanon
  have p0069 :=
    @gAnbi2i
      (synWral n (synCnnc) (.imp (.classMem (.cv n)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))
      (synWral z (synCnnc) (.imp (.classMem (.cv z)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
          (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
      p0068
  have p0070 :=
    @gAnbi2i
      (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWral n (synCnnc) (.imp (.classMem (.cv n)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
      (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
            (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
        (synWral z (synCnnc) (.imp (.classMem (.cv z)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))
      (.classMem (.cv k) (synCnnc)) p0069
  have p0071 :=
    @gBiimpri
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral n (synCnnc) (.imp (.classMem (.cv n)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      p0070
  have p0072 := @gId (.classEq (.cv y) (.cv r))
  have p0073 :=
    @gBreq2d (.classEq (.cv y) (.cv r)) (.cv y) (.cv r) (synCtc C) (synClec) p0072
  have p0074 := @gId (.classEq (.cv y) (.cv r))
  have p0075 :=
    @gFveq2d (.classEq (.cv y) (.cv r)) (.cv y) (.cv r) (synCwppstopstep F C) p0074
  have p0076 :=
    @gBreq2d (.classEq (.cv y) (.cv r)) (synCfv (synCwppstopstep F C) (.cv y))
      (synCfv (synCwppstopstep F C) (.cv r)) C (synClec) p0075
  have p0077 :=
    @gImbi12d (.classEq (.cv y) (.cv r)) (synWbr (synCtc C) (synClec) (.cv y))
      (synWbr (synCtc C) (synClec) (.cv r))
      (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))
      (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r))) p0073 p0076
  have p0078_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y r) (synWb (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))
          (.imp (synWbr (synCtc C) (synClec) (.cv r))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCtc synCio synCuni synCsn synClec synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0078 :=
    @gCbvralv
      (.imp (synWbr (synCtc C) (synClec) (.cv y))
        (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))
      (.imp (synWbr (synCtc C) (synClec) (.cv r))
        (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r))))
      y r (synCdm (synCwppstopstep F C)) dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 p0078_e00_recanon
  have p0079 :=
    @gBiimpri
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
      (synWral r (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv r))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))
      p0078
  have p0080 :=
    @gWppstopfixedhitcontrgrowfixdndv
      (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      (synWral r (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv r))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))
      x y C k m n F (synCwppgamma (synCwppstopstep F C) C) p dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0037 dv_cache_0005 dv_cache_0038 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0039 dv_cache_0010 dv_cache_0040 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0011 dv_cache_0012 dv_cache_0056 dv_cache_0014
      dv_cache_0057 dv_cache_0015 dv_cache_0058 dv_cache_0017 dv_cache_0059 dv_cache_0060
      dv_cache_0061 dv_cache_0062 dv_cache_0019 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0041 dv_cache_0042 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
      dv_cache_0043 hyp_wppstopgammacontrgrowthstagedndv_1
      hyp_wppstopgammacontrgrowthstagedndv_2 hyp_wppstopgammacontrgrowthstagedndv_3
      hyp_wppstopgammacontrgrowthstagedndv_4 hyp_wppstopgammacontrgrowthstagedndv_5
      hyp_wppstopgammacontrgrowthstagedndv_6 p0053 hyp_wppstopgammacontrgrowthstagedndv_7
      p0062 p0071 p0079
  have p0081 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
        (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))
      (.classEq (synCwppgamma (synCwppstopstep F C) C)
        (synCtc (synCwppgamma (synCwppstopstep F C) C)))
      (.imp (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))) (synWa
            (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWral z (synCnnc) (.imp (.classMem (.cv z)
                      (synCwpphit (synCwppstopstep F (synCtc C))
                        (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                    (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
            (synWral r (synCdm (synCwppstopstep F C))
              (.imp (synWbr (synCtc C) (synClec) (.cv r))
                (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))))
        (.neg (.classEq (synC0c) (synC0c))))
      p0052 p0080
  have p0082 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
                (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F C)
                      (synCwppgamma (synCwppstopstep F C) C) C))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
        (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y))))))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z)))))) (synWa
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWral z (synCnnc) (.imp (.classMem (.cv z)
                    (synCwpphit (synCwppstopstep F (synCtc C))
                      (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
          (synWral r (synCdm (synCwppstopstep F C))
            (.imp (synWbr (synCtc C) (synClec) (.cv r))
              (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv r)))))))
      (.neg (.classEq (synC0c) (synC0c))) p0047 p0081
  have p0083 :=
    @gEx
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (synWral y (synCdm (synCwppstopstep F C))
        (.imp (synWbr (synCtc C) (synClec) (.cv y))
          (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
      (.neg (.classEq (synC0c) (synC0c))) p0082
  have p0084 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) (synWa
          (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa
            (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k)
              (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral z (synCnnc) (.imp (.classMem (.cv z)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))))))
      (.imp (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
        (.neg (.classEq (synC0c) (synC0c))))
      p0031 p0083
  have p0085 :=
    @gEx (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      (.imp (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
        (.neg (.classEq (synC0c) (synC0c))))
      p0084
  have p0086 :=
    @gRexlimivv
      (synWa (synWa (.classMem (.cv m)
            (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
          (synWral z (synCnnc) (.imp (.classMem (.cv z) (synCwpphit (synCwppstopstep F C)
                  (synCwppgamma (synCwppstopstep F C) C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv z))))) (synWa (.classMem (.cv k)
            (synCwpphit (synCwppstopstep F (synCtc C))
              (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
          (synWral z (synCnnc) (.imp (.classMem (.cv z)
                (synCwpphit (synCwppstopstep F (synCtc C))
                  (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))))))
      (.imp (synWral y (synCdm (synCwppstopstep F C))
          (.imp (synWbr (synCtc C) (synClec) (.cv y))
            (synWbr C (synClec) (synCfv (synCwppstopstep F C) (.cv y)))))
        (.neg (.classEq (synC0c) (synC0c))))
      m k (synCnnc) (synCnnc) dv_cache_0028 dv_cache_0070 dv_cache_0071 dv_cache_0032
      p0085
  have p0087 := Nominal.mp p0020 p0086
  exact p0087


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part069`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as
`g_wppconcrete6globalnonfixedfromhnshiftndv`.
-/
@[expose]
noncomputable def gWppconcrete6globalnonfixedfromhnshiftndv (y : Var)
    (hyp_wppconcrete6globalnonfixedfromhnshiftndv_1 : Nominal.NPrf (.neg (synWbr (synChncard
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synClec) (synCtc (synCtc (synCnc (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))) :
    Nominal.NPrf
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y)) (synWne (.cv y) (synCtc (.cv y))))) :=
  by
  have p0000 := @gHncardtc6oneeqndv
  have p0001 :=
    @gBreq1i
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCtc (synCtc (synCnc
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synClec) p0000
  have p0002 :=
    @gMtbir
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWbr (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synClec) (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      hyp_wppconcrete6globalnonfixedfromhnshiftndv_1 p0001
  have p0003 :=
    @gA1i
      (.neg (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCtc (synCtc (synCnc (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)))
      p0002
  have p0004 :=
    @gSimpl
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)))
      (.classEq (.cv y) (synCtc (.cv y)))
  have p0005 :=
    @gSimprd
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (.cv y))
      p0004
  have p0007 :=
    @gSimpld
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (.cv y))
      p0004
  have p0008 := @gHwcardssnc (synCvv)
  have p0009 := @gSseli (synChwcards (synCvv)) (synCncs) (.cv y) p0008
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synChwcards (synCvv))) (.classMem (.cv y) (synCncs)) p0007
      p0009
  have p0011 := @gTlenc1c (.cv y)
  have p0012 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs))
      (synWbr (synCtc (.cv y)) (synClec) (synCnc (synC1c))) p0010 p0011
  have p0013 :=
    @gSimpr
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)))
      (.classEq (.cv y) (synCtc (.cv y)))
  have p0014 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y)) (synCnc (synC1c)) (synClec) p0013
  have p0015 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCnc (synC1c)))
      (synWbr (synCtc (.cv y)) (synClec) (synCnc (synC1c))) p0012 p0014
  have p0021 := @gN1cex
  have p0022 := @gNcelncsi (synC1c) p0021
  have p0023 :=
    @gA1i (.classMem (synCnc (synC1c)) (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0022
  have p0024 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs)) (.classMem (synCnc (synC1c)) (synCncs)) p0010
      p0023
  have p0025 := @gTlecg (.cv y) (synCnc (synC1c))
  have p0026 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (.classMem (.cv y) (synCncs)) (.classMem (synCnc (synC1c)) (synCncs)))
      (synWb (synWbr (.cv y) (synClec) (synCnc (synC1c)))
        (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCnc (synC1c)))))
      p0024 p0025
  have p0027 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCnc (synC1c)))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCnc (synC1c)))) p0015 p0026
  have p0029 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y)) (synCtc (synCnc (synC1c))) (synClec) p0013
  have p0030 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCnc (synC1c))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCnc (synC1c)))) p0027 p0029
  have p0038 := @gTccl (synCnc (synC1c))
  have p0039 := Nominal.mp p0022 p0038
  have p0040 :=
    @gA1i (.classMem (synCtc (synCnc (synC1c))) (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0039
  have p0041 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs)) (.classMem (synCtc (synCnc (synC1c))) (synCncs))
      p0010 p0040
  have p0042 := @gTlecg (.cv y) (synCtc (synCnc (synC1c)))
  have p0043 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (.classMem (.cv y) (synCncs))
        (.classMem (synCtc (synCnc (synC1c))) (synCncs)))
      (synWb (synWbr (.cv y) (synClec) (synCtc (synCnc (synC1c))))
        (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc (synCnc (synC1c))))))
      p0041 p0042
  have p0044 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCnc (synC1c))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc (synCnc (synC1c))))) p0030
      p0043
  have p0046 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y)) (synCtc (synCtc (synCnc (synC1c)))) (synClec) p0013
  have p0047 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCnc (synC1c)))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc (synCnc (synC1c))))) p0044
      p0046
  have p0057 := @gTccl (synCtc (synCnc (synC1c)))
  have p0058 := Nominal.mp p0039 p0057
  have p0059 :=
    @gA1i (.classMem (synCtc (synCtc (synCnc (synC1c)))) (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0058
  have p0060 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs))
      (.classMem (synCtc (synCtc (synCnc (synC1c)))) (synCncs)) p0010 p0059
  have p0061 := @gTlecg (.cv y) (synCtc (synCtc (synCnc (synC1c))))
  have p0062 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (.classMem (.cv y) (synCncs))
        (.classMem (synCtc (synCtc (synCnc (synC1c)))) (synCncs)))
      (synWb (synWbr (.cv y) (synClec) (synCtc (synCtc (synCnc (synC1c)))))
        (synWbr (synCtc (.cv y)) (synClec)
          (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
      p0060 p0061
  have p0063 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCnc (synC1c)))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc (synCtc (synCnc (synC1c))))))
      p0047 p0062
  have p0065 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y)) (synCtc (synCtc (synCtc (synCnc (synC1c)))))
      (synClec) p0013
  have p0066 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCtc (synCnc (synC1c))))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc (synCtc (synCnc (synC1c))))))
      p0063 p0065
  have p0078 := @gTccl (synCtc (synCtc (synCnc (synC1c))))
  have p0079 := Nominal.mp p0058 p0078
  have p0080 :=
    @gA1i (.classMem (synCtc (synCtc (synCtc (synCnc (synC1c))))) (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0079
  have p0081 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCnc (synC1c))))) (synCncs)) p0010 p0080
  have p0082 := @gTlecg (.cv y) (synCtc (synCtc (synCtc (synCnc (synC1c)))))
  have p0083 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (.classMem (.cv y) (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCnc (synC1c))))) (synCncs)))
      (synWb (synWbr (.cv y) (synClec) (synCtc (synCtc (synCtc (synCnc (synC1c))))))
        (synWbr (synCtc (.cv y)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
      p0081 p0082
  have p0084 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCtc (synCnc (synC1c))))))
      (synWbr (synCtc (.cv y)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
      p0066 p0083
  have p0086 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y))
      (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))) (synClec) p0013
  have p0087 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
      (synWbr (synCtc (.cv y)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
      p0084 p0086
  have p0101 := @gTccl (synCtc (synCtc (synCtc (synCnc (synC1c)))))
  have p0102 := Nominal.mp p0079 p0101
  have p0103 :=
    @gA1i
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))) (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0102
  have p0104 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))) (synCncs))
      p0010 p0103
  have p0105 :=
    @gTlecg (.cv y) (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))
  have p0106 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (.classMem (.cv y) (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))) (synCncs)))
      (synWb (synWbr (.cv y) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
        (synWbr (synCtc (.cv y)) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
      p0104 p0105
  have p0107 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
      (synWbr (synCtc (.cv y)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
      p0087 p0106
  have p0109 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))) (synClec)
      p0013
  have p0110 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
      (synWbr (synCtc (.cv y)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
      p0107 p0109
  have p0126 := @gTccl (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))
  have p0127 := Nominal.mp p0102 p0126
  have p0128 :=
    @gA1i
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
        (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0127
  have p0129 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
        (synCncs))
      p0010 p0128
  have p0130 :=
    @gTlecg (.cv y) (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
  have p0131 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (.classMem (.cv y) (synCncs))
        (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
          (synCncs)))
      (synWb (synWbr (.cv y) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
        (synWbr (synCtc (.cv y)) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))
      p0129 p0130
  have p0132 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
      (synWbr (synCtc (.cv y)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
      p0110 p0131
  have p0134 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
      (synClec) p0013
  have p0135 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
      (synWbr (synCtc (.cv y)) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
      p0132 p0134
  have p0153 :=
    @gTccl (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
  have p0154 := Nominal.mp p0127 p0153
  have p0155 :=
    @gA1i
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
        (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0154
  have p0156 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs))
      (.classMem (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
        (synCncs))
      p0010 p0155
  have p0157 :=
    @gTlecg (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
  have p0158 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (.classMem (.cv y) (synCncs)) (.classMem
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
          (synCncs)))
      (synWb (synWbr (.cv y) (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
        (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))))
      p0156 p0157
  have p0159 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))
      p0135 p0158
  have p0161 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
      (synClec) p0013
  have p0162 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))
      p0159 p0161
  have p0182 :=
    @gTccl
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
  have p0183 := Nominal.mp p0154 p0182
  have p0184 :=
    @gA1i
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
        (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0183
  have p0185 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (.cv y) (synCncs))
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
        (synCncs))
      p0010 p0184
  have p0186 :=
    @gTlecg (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
  have p0187 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (.classMem (.cv y) (synCncs)) (.classMem (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
          (synCncs)))
      (synWb (synWbr (.cv y) (synClec) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))
        (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))))
      p0185 p0186
  have p0188 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))))
      p0162 p0187
  have p0190 :=
    @gBreq1d
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.cv y) (synCtc (.cv y))
      (synCtc (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))
      (synClec) p0013
  have p0191 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))))
      (synWbr (synCtc (.cv y)) (synClec) (synCtc (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))))
      p0188 p0190
  have p0192 := @gTcnc1c
  have p0193 := @gTceq (synCtc (synCnc (synC1c))) (synCnc (synCpw1 (synC1c)))
  have p0194 := Nominal.mp p0192 p0193
  have p0196 := @gPw1ex (synC1c) p0021
  have p0197 := @gTcnc (synCpw1 (synC1c)) p0196
  have p0198 :=
    @gEqtri (synCtc (synCtc (synCnc (synC1c))))
      (synCtc (synCnc (synCpw1 (synC1c)))) (synCnc (synCpw1 (synCpw1 (synC1c))))
      p0194 p0197
  have p0199 :=
    @gTceq (synCtc (synCtc (synCnc (synC1c))))
      (synCnc (synCpw1 (synCpw1 (synC1c))))
  have p0200 := Nominal.mp p0198 p0199
  have p0203 := @gPw1ex (synCpw1 (synC1c)) p0196
  have p0204 := @gTcnc (synCpw1 (synCpw1 (synC1c))) p0203
  have p0205 :=
    @gEqtri (synCtc (synCtc (synCtc (synCnc (synC1c)))))
      (synCtc (synCnc (synCpw1 (synCpw1 (synC1c)))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0200 p0204
  have p0206 :=
    @gTceq (synCtc (synCtc (synCtc (synCnc (synC1c)))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  have p0207 := Nominal.mp p0205 p0206
  have p0211 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0203
  have p0212 := @gTcnc (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0211
  have p0213 :=
    @gEqtri (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))
      (synCtc (synCnc (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0207 p0212
  have p0214 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  have p0215 := Nominal.mp p0213 p0214
  have p0220 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0211
  have p0221 := @gTcnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0220
  have p0222 :=
    @gEqtri (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
      (synCtc (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0215
      p0221
  have p0223 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
  have p0224 := Nominal.mp p0222 p0223
  have p0230 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0220
  have p0231 :=
    @gTcnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0230
  have p0232 :=
    @gEqtri
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
      (synCtc (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0224 p0231
  have p0233 :=
    @gTceq
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  have p0234 := Nominal.mp p0232 p0233
  have p0235 :=
    @gTceq
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))
      (synCtc (synCnc
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
  have p0236 := Nominal.mp p0234 p0235
  have p0237 :=
    @gBreq2i
      (synCtc (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c))))))))))
      (synCtc (synCtc (synCnc
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (.cv y) (synClec) p0236
  have p0238 :=
    @gSylib
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (synC1c)))))))))))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0191 p0237
  have p0239 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (.cv y))
      (synWbr (.cv y) (synClec) (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0005 p0238
  have p0240 := @gHncardnc1ndv
  have p0241 := @gTccl (synChncard (synC1c))
  have p0242 := Nominal.mp p0240 p0241
  have p0243 := @gTccl (synCtc (synChncard (synC1c)))
  have p0244 := Nominal.mp p0242 p0243
  have p0245 := @gTccl (synCtc (synCtc (synChncard (synC1c))))
  have p0246 := Nominal.mp p0244 p0245
  have p0247 := @gTccl (synCtc (synCtc (synCtc (synChncard (synC1c)))))
  have p0248 := Nominal.mp p0246 p0247
  have p0249 := @gTccl (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
  have p0250 := Nominal.mp p0248 p0249
  have p0251 :=
    @gTccl (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
  have p0252 := Nominal.mp p0250 p0251
  have p0253 :=
    @gA1i
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0252
  have p0265 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0230
  have p0266 :=
    @gNcelncsi
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0265
  have p0267 :=
    @gTccl
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  have p0268 := Nominal.mp p0266 p0267
  have p0269 :=
    @gTccl
      (synCtc (synCnc
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
  have p0270 := Nominal.mp p0268 p0269
  have p0271 :=
    @gA1i
      (.classMem (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) (synCncs))
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      p0270
  have p0272 :=
    @gN3jca
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synCncs))
      (.classMem (.cv y) (synCncs))
      (.classMem (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) (synCncs))
      p0253 p0010 p0271
  have p0273 :=
    @gLectr
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (.cv y)
      (synCtc (synCtc (synCnc
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
  have p0274 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synW3a (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synCncs)) (.classMem (.cv y) (synCncs)) (.classMem (synCtc (synCtc (synCnc
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
          (synCncs)))
      (.imp (synWa (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y)) (synWbr (.cv y) (synClec) (synCtc (synCtc (synCnc (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
        (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCtc (synCtc (synCnc (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      p0272 p0273
  have p0275 :=
    @gMpd
      (synWa (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (.cv y))) (.classEq (.cv y) (synCtc (.cv y))))
      (synWa (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)) (synWbr (.cv y) (synClec) (synCtc (synCtc (synCnc (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0239 p0274
  have p0276 :=
    @gEx
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)))
      (.classEq (.cv y) (synCtc (.cv y)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0275
  have p0277 :=
    @gMtod
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)))
      (.classEq (.cv y) (synCtc (.cv y)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCtc (synCtc (synCnc (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0003 p0276
  have p0278 := (Nominal.biimpRefl (synWne (.cv y) (synCtc (.cv y))))
  have p0279 :=
    @gA1i
      (synWb (synWne (.cv y) (synCtc (.cv y))) (.neg (.classEq (.cv y) (synCtc (.cv y)))))
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)))
      p0278
  have p0280 :=
    @gMpbird
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)))
      (synWne (.cv y) (synCtc (.cv y))) (.neg (.classEq (.cv y) (synCtc (.cv y))))
      p0277 p0279
  have p0281 :=
    @gEx (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (.cv y))
      (synWne (.cv y) (synCtc (.cv y))) p0280
  have p0282 :=
    @gRgen
      (.imp (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)) (synWne (.cv y) (synCtc (.cv y))))
      y (synChwcards (synCvv)) p0281
  exact p0282

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6rnhwcardsndv`. -/
@[expose]
noncomputable def gWppconcrete6rnhwcardsndv :
    Nominal.NPrf (synWss (synCrn (synCwppconcrete6fn)) (synChwcards (synCvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let u : Var := freshVar proofSupport 0
  have p0000 := @gPwexg (.cv u) (synCvv)
  have p0001 := @gPwexg (synCpw (.cv u)) (synCvv)
  have p0002 :=
    @gSyl (.classMem (.cv u) (synCvv)) (.classMem (synCpw (.cv u)) (synCvv))
      (.classMem (synCpw (synCpw (.cv u))) (synCvv)) p0000 p0001
  have p0003 := @gHnordexg (synCpw (synCpw (.cv u)))
  have p0004 :=
    @gSyl (.classMem (.cv u) (synCvv)) (.classMem (synCpw (synCpw (.cv u))) (synCvv))
      (.classMem (synChnord (synCpw (synCpw (.cv u)))) (synCvv)) p0002 p0003
  have p0005 := @gHncardhwcardsndv (synChnord (synCpw (synCpw (.cv u))))
  have p0006 :=
    @gSyl (.classMem (.cv u) (synCvv))
      (.classMem (synChnord (synCpw (synCpw (.cv u)))) (synCvv))
      (.classMem (synChncard (synChnord (synCpw (synCpw (.cv u)))))
        (synChwcards (synCvv)))
      p0004 p0005
  have p0007 :=
    @gRgen
      (.classMem (synChncard (synChnord (synCpw (synCpw (.cv u)))))
        (synChwcards (synCvv)))
      u (synCvv) p0006
  have p0008 := @gWppconcrete6rnhwcardsredndv u p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as
`g_wppconcrete6thresholdhwcardsndv`.
-/
@[expose]
noncomputable def gWppconcrete6thresholdhwcardsndv :
    Nominal.NPrf
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synChwcards (synCvv))) :=
  by
  have p0000 := @gHncardtc6oneeqndv
  have p0001 := @gN1cex
  have p0002 := @gPw1ex (synC1c) p0001
  have p0003 := @gPw1ex (synCpw1 (synC1c)) p0002
  have p0004 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0003
  have p0005 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0004
  have p0006 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0005
  have p0007 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0006
  have p0008 :=
    @gHncardhwcardsndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gEqeltri
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synChwcards (synCvv)) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as
`g_wppconcrete6stoppedtchomfullndv`.
-/
@[expose]
noncomputable def gWppconcrete6stoppedtchomfullndv (x : Var) :
    Nominal.NPrf
      (synWral x (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (.classEq (synCtc (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv x)))
          (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synCtc (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  let u : Var := freshVar proofSupport 0
  have p0000 := @gPwexg (.cv u) (synCvv)
  have p0001 := @gPwexg (synCpw (.cv u)) (synCvv)
  have p0002 :=
    @gSyl (.classMem (.cv u) (synCvv)) (.classMem (synCpw (.cv u)) (synCvv))
      (.classMem (synCpw (synCpw (.cv u))) (synCvv)) p0000 p0001
  have p0003 := @gHnordexg (synCpw (synCpw (.cv u)))
  have p0004 :=
    @gSyl (.classMem (.cv u) (synCvv)) (.classMem (synCpw (synCpw (.cv u))) (synCvv))
      (.classMem (synChnord (synCpw (synCpw (.cv u)))) (synCvv)) p0002 p0003
  have p0005 := @gHncardhwcardsndv (synChnord (synCpw (synCpw (.cv u))))
  have p0006 :=
    @gSyl (.classMem (.cv u) (synCvv))
      (.classMem (synChnord (synCpw (synCpw (.cv u)))) (synCvv))
      (.classMem (synChncard (synChnord (synCpw (synCpw (.cv u)))))
        (synChwcards (synCvv)))
      p0004 p0005
  have p0007 :=
    @gRgen
      (.classMem (synChncard (synChnord (synCpw (synCpw (.cv u)))))
        (synChwcards (synCvv)))
      u (synCvv) p0006
  have p0008 := @gWppconcrete6rnhwcardsredndv u p0007
  have p0009 := @gHncardtc6oneeqndv
  have p0010 := @gN1cex
  have p0011 := @gPw1ex (synC1c) p0010
  have p0012 := @gPw1ex (synCpw1 (synC1c)) p0011
  have p0013 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0012
  have p0014 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0013
  have p0015 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0014
  have p0016 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0015
  have p0017 :=
    @gHncardhwcardsndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gEqeltri
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synChwcards (synCvv)) p0009 p0018
  have p0020 := @gWppconcrete6stoppedtchomndv x p0008 p0019
  exact p0020


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part070`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as
`g_wppconcrete6stoppedgammacontrgrowthstagedndv`.
-/
@[expose]
noncomputable def gWppconcrete6stoppedgammacontrgrowthstagedndv (y : Var)
    (hyp_wppconcrete6stoppedgammacontrgrowthstagedndv_1 : Nominal.NPrf (.neg (synWbr
            (synChncard
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synClec) (synCtc (synCtc (synCnc (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))) :
    Nominal.NPrf
      (.imp (synWral y (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))) (.imp
            (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y)) (synWbr (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
              (synClec) (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
                (.cv y))))) (.neg (.classEq (synC0c) (synC0c)))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact fresh_x (Finset.mem_singleton.mpr h)
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact fresh_p (Finset.mem_singleton.mpr h)
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have dv_cache_0001 :
    p ∉
      ((synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 :
    y ∉
      ((synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 : p ∉ ((synCwppconcrete6fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synCwppconcrete6fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synCwppconcrete6fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0008 : p ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show p ≠ y from (by exact fresh_p_ne_y))
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gWppconcrete6fnfunsndv
  have p0001 := @gWppconcrete6rnhwcardsndv
  have p0002 := @gWppconcrete6thresholdhwcardsndv
  have p0003 := @gWppconcrete6thresholdtclecndv
  have p0004 := @gWppconcrete6hncard1dmcovndv p
  have p0005 := @gWppconcrete6stoppedtchomfullndv x
  have p0006 :=
    @gWppconcrete6globalnonfixedfromhnshiftndv y
      hyp_wppconcrete6stoppedgammacontrgrowthstagedndv_1
  have p0007 :=
    @gWppstopgammacontrgrowthstagedndv x y
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCwppconcrete6fn) p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0000 p0001
      p0002 p0003 p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeselfnoisoclndv`. -/
@[expose]
noncomputable def gHnwcutcodeselfnoisoclndv (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
        (.neg (synWbr B (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0002 : v ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_B, not_false_eq_true])
  have dv_cache_0003 :
    v ∉
      ((Wff.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
          (.neg (synWbr B (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_B, fresh_v_not_A, fresh_v_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gId (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
  have p0001 :=
    @gSimpl (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B))
  have p0002 := @gElex B (synChwcn A)
  have p0003 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
      (.classMem B (synChwcn A)) (.classMem B (synCvv)) p0001 p0002
  have p0004 := @gId (.classEq (.cv v) B)
  have p0005 := @gEleq1d (.classEq (.cv v) B) (.cv v) B (synChwcn A) p0004
  have p0007 := @gFveq2d (.classEq (.cv v) B) (.cv v) B (synC2nd) p0004
  have p0008 :=
    @gEleq2d (.classEq (.cv v) B) (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) B)
      (.cv x) p0007
  have p0009 :=
    @gAnbi12d (.classEq (.cv v) B) (.classMem (.cv v) (synChwcn A))
      (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv x) (synCfv (synC2nd) B)) p0005 p0008
  have p0012 := @gFveq2d (.classEq (.cv v) B) (.cv v) B (synC1st) p0004
  have p0015 :=
    @gJca (.classEq (.cv v) B)
      (.classEq (synCfv (synC1st) (.cv v)) (synCfv (synC1st) B))
      (.classEq (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) B)) p0012 p0007
  have p0016 :=
    @gHnwcutcodeeq12ndv x (synCfv (synC2nd) (.cv v)) (synCfv (synC1st) (.cv v))
      (synCfv (synC1st) B) (synCfv (synC2nd) B)
  have p0017 :=
    @gSyl (.classEq (.cv v) B)
      (synWa (.classEq (synCfv (synC1st) (.cv v)) (synCfv (synC1st) B))
        (.classEq (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) B)))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x)))
      p0015 p0016
  have p0018 :=
    @gBreq12d (.classEq (.cv v) B) (.cv v) B
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x))
      (synChwniso A) p0004 p0017
  have p0019 :=
    @gNotbid (.classEq (.cv v) B)
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWbr B (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x)))
      p0018
  have p0020 :=
    @gImbi12d (.classEq (.cv v) B)
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
      (.neg (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.neg (synWbr B (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x))))
      p0009 p0019
  have p0021 := @gHnwcutcodeselfnoisondv x v A dv_cache_0001
  have p0022 :=
    @gVtoclg
      (.imp (synWa (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))) (.neg
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
        (.neg (synWbr B (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x)))))
      v B (synCvv) dv_cache_0002 dv_cache_0003 p0020 p0021
  have p0023 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
      (.classMem B (synCvv))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
        (.neg (synWbr B (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x)))))
      p0003 p0022
  have p0024 :=
    @gMpd (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
      (synWa (.classMem B (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) B)))
      (.neg (synWbr B (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B) (.cv x))))
      p0000 p0023
  exact p0024


end NFChoice.DirectNominalPrf.WPPReplay

end
