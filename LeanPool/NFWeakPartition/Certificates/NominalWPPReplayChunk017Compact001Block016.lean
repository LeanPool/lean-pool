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

@[expose]
noncomputable def g_wppstopgammacontrgrowthstagedndv (x : Var) (y : Var) (C : Class)
    (F : Class) (p : Var) (dv_C_p : p ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_F_p : p ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_p_x : p ≠ x)
    (dv_p_y : p ≠ y) (dv_x_y : x ≠ y)
    (hyp_wppstopgammacontrgrowthstagedndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopgammacontrgrowthstagedndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammacontrgrowthstagedndv_3 :
      Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammacontrgrowthstagedndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C))
    (hyp_wppstopgammacontrgrowthstagedndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))))
    (hyp_wppstopgammacontrgrowthstagedndv_6 : Nominal.NPrf
        (syn_wral x (syn_cdm (syn_cwppstopstep F C))
          (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))))))
    (hyp_wppstopgammacontrgrowthstagedndv_7 : Nominal.NPrf (syn_wral y (syn_chwcards (syn_cvv))
          (.imp (syn_wbr C (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y)))))) :
    Nominal.NPrf
      (.imp (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
        (.neg (.classEq (syn_c0c) (syn_c0c)))) :=
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
  have dv_cache_0021 : n ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0022 : z ∉ ((syn_cnnc)).fv :=
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
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))).fv :=
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
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))).fv :=
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
  have dv_cache_0025 : q ∉ ((syn_cnnc)).fv :=
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
      ((Wff.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))).fv :=
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
      ((Wff.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))).fv :=
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
  have dv_cache_0028 : k ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0029 : m ∉ ((syn_cnnc)).fv :=
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
      ((syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))).fv :=
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
      ((syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))).fv :=
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
  have dv_cache_0033 : y ∉ ((syn_cdm (syn_cwppstopstep F C))).fv :=
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
  have dv_cache_0034 : r ∉ ((syn_cdm (syn_cwppstopstep F C))).fv :=
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
      ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))).fv :=
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
      ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r))))).fv :=
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
      ((Wff.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))).fv :=
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
      ((Wff.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))).fv :=
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
  have dv_cache_0046 : k ∉ ((syn_cwppgamma (syn_cwppstopstep F C) C)).fv :=
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
  have dv_cache_0047 : m ∉ ((syn_cwppgamma (syn_cwppstopstep F C) C)).fv :=
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
  have dv_cache_0048 : n ∉ ((syn_cwppgamma (syn_cwppstopstep F C) C)).fv :=
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
  have dv_cache_0049 : p ∉ ((syn_cwppgamma (syn_cwppstopstep F C) C)).fv :=
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
  have dv_cache_0050 : x ∉ ((syn_cwppgamma (syn_cwppstopstep F C) C)).fv :=
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
  have dv_cache_0051 : y ∉ ((syn_cwppgamma (syn_cwppstopstep F C) C)).fv :=
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
      ((syn_wral r (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))).fv :=
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
      ((syn_wral r (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))).fv :=
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
      ((syn_wral r (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))).fv :=
    by
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
      ((syn_wral r (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))).fv :=
    by
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
      ((syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
      ((syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
      ((syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
      ((syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
      ((Wff.imp (syn_wral y (syn_cdm (syn_cwppstopstep F C))
            (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
              (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
          (.neg (.classEq (syn_c0c) (syn_c0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
      ((Wff.imp (syn_wral y (syn_cdm (syn_cwppstopstep F C))
            (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
              (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
          (.neg (.classEq (syn_c0c) (syn_c0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
    @g_wppstopgammaleasthitpairndv x C k m n F q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      hyp_wppstopgammacontrgrowthstagedndv_1 hyp_wppstopgammacontrgrowthstagedndv_2
      hyp_wppstopgammacontrgrowthstagedndv_3 hyp_wppstopgammacontrgrowthstagedndv_6
  have p0001 := @g_id (.classEq (.cv n) (.cv z))
  have p0002 :=
    @g_eleq1d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z)
      (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C)
      p0001
  have p0003 := @g_id (.classEq (.cv n) (.cv z))
  have p0004 :=
    @g_breq2d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z) (.cv m) (syn_ckqrel (syn_clefin))
      p0003
  have p0005 :=
    @g_imbi12d (.classEq (.cv n) (.cv z))
      (.classMem (.cv n)
        (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
      (.classMem (.cv z)
        (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)) p0002 p0004
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n z) (syn_wb (.imp (.classMem (.cv n)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint
          syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
          syn_cwppstopstep syn_cwppgamma syn_cio syn_cuni
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_cbvralv
      (.imp (.classMem (.cv n)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))
      (.imp (.classMem (.cv z)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))
      n z (syn_cnnc) dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      p0006_e00_recanon
  have p0007 :=
    @g_anbi2i
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))
      (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv m)
        (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
      p0006
  have p0008 :=
    @g_rexbii
      (syn_wa (.classMem (.cv m)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))
      (syn_wa (.classMem (.cv m)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))
      m (syn_cnnc) p0007
  have p0009 := @g_id (.classEq (.cv q) (.cv z))
  have p0010 :=
    @g_eleq1d (.classEq (.cv q) (.cv z)) (.cv q) (.cv z)
      (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
        (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C))
      p0009
  have p0011 := @g_id (.classEq (.cv q) (.cv z))
  have p0012 :=
    @g_breq2d (.classEq (.cv q) (.cv z)) (.cv q) (.cv z) (.cv k) (syn_ckqrel (syn_clefin))
      p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv q) (.cv z))
      (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
          (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
      (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
          (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)) p0010 p0012
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq q z) (syn_wb (.imp (.classMem (.cv q)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint
          syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
          syn_cwppstopstep syn_ctc syn_cio syn_cuni
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @g_cbvralv
      (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))
      (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))
      q z (syn_cnnc) dv_cache_0025 dv_cache_0022 dv_cache_0026 dv_cache_0027
      p0014_e00_recanon
  have p0015 :=
    @g_anbi2i
      (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))
      (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
          (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
      p0014
  have p0016 :=
    @g_rexbii
      (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))
      (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))
      k (syn_cnnc) p0015
  have p0017 :=
    @g_anbi12i
      (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))
      (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      p0008 p0016
  have p0018 :=
    @g_mpbi
      (syn_wa (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wrex k (syn_cnnc)
          (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))))
      (syn_wa (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))) (syn_wrex k (syn_cnnc)
          (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      p0000 p0017
  have p0019 :=
    @g_reeanv
      (syn_wa (.classMem (.cv m)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))
      (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))
      m k (syn_cnnc) (syn_cnnc) dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
      dv_cache_0032
  have p0020 :=
    @g_mpbir
      (syn_wrex m (syn_cnnc) (syn_wrex k (syn_cnnc) (syn_wa (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
              (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))))
      (syn_wa (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))) (syn_wrex k (syn_cnnc)
          (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      p0018 p0019
  have p0021 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
  have p0022 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa
          (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
            (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) p0021
  have p0023 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
  have p0024 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa
          (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
            (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (syn_wa (.classMem (.cv m)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))
      (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))
      p0023
  have p0025 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa
          (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
            (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (.classMem (.cv m) (syn_cnnc))
      (syn_wa (.classMem (.cv m)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))
      p0022 p0024
  have p0027 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa
          (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
            (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) p0021
  have p0029 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa
          (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
            (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (syn_wa (.classMem (.cv m)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))
      (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))
      p0023
  have p0030 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa
          (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
            (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))
      p0027 p0029
  have p0031 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa
          (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
            (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      p0025 p0030
  have p0032 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
  have p0033 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
        (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      p0032
  have p0035 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
        (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      p0032
  have p0036 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
  have p0037 := @g_id (.classEq (.cv y) (.cv r))
  have p0038 :=
    @g_breq2d (.classEq (.cv y) (.cv r)) (.cv y) (.cv r) (syn_ctc C) (syn_clec) p0037
  have p0039 := @g_id (.classEq (.cv y) (.cv r))
  have p0040 :=
    @g_fveq2d (.classEq (.cv y) (.cv r)) (.cv y) (.cv r) (syn_cwppstopstep F C) p0039
  have p0041 :=
    @g_breq2d (.classEq (.cv y) (.cv r)) (syn_cfv (syn_cwppstopstep F C) (.cv y))
      (syn_cfv (syn_cwppstopstep F C) (.cv r)) C (syn_clec) p0040
  have p0042 :=
    @g_imbi12d (.classEq (.cv y) (.cv r)) (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
      (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r))) p0038 p0041
  have p0043_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y r) (syn_wb (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_ctc syn_cio syn_cuni syn_csn syn_clec syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0042
  have p0043 :=
    @g_cbvralv
      (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))
      (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r))))
      y r (syn_cdm (syn_cwppstopstep F C)) dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 p0043_e00_recanon
  have p0044 :=
    @g_biimpi
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
      (syn_wral r (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))
      p0043
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
        (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
      (syn_wral r (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))
      p0036 p0044
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
        (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (syn_wral r (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))
      p0035 p0045
  have p0047 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
        (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
        (syn_wral r (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r))))))
      p0033 p0046
  have p0049 :=
    @g_wppstopgammafixedhwdndv x y C F p dv_cache_0037 dv_cache_0005 dv_cache_0038
      dv_cache_0039 dv_cache_0010 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
      hyp_wppstopgammacontrgrowthstagedndv_1 hyp_wppstopgammacontrgrowthstagedndv_2
      hyp_wppstopgammacontrgrowthstagedndv_3 hyp_wppstopgammacontrgrowthstagedndv_4
      hyp_wppstopgammacontrgrowthstagedndv_5 hyp_wppstopgammacontrgrowthstagedndv_6
  have p0050 :=
    @g_simprd
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
      (.classEq (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C))
        (syn_cwppgamma (syn_cwppstopstep F C) C))
      p0049
  have p0051 :=
    @g_eqcomd
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C))
      (syn_cwppgamma (syn_cwppstopstep F C) C) p0050
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
        (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
      (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C)
        (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)))
      p0036 p0051
  have p0053 :=
    @g_wppstopgammahwndv C F hyp_wppstopgammacontrgrowthstagedndv_1
      hyp_wppstopgammacontrgrowthstagedndv_2 hyp_wppstopgammacontrgrowthstagedndv_3
  have p0054 := @g_id (.classEq (.cv n) (.cv z))
  have p0055 :=
    @g_eleq1d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z)
      (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C)
      p0054
  have p0056 := @g_id (.classEq (.cv n) (.cv z))
  have p0057 :=
    @g_breq2d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z) (.cv m) (syn_ckqrel (syn_clefin))
      p0056
  have p0058 :=
    @g_imbi12d (.classEq (.cv n) (.cv z))
      (.classMem (.cv n)
        (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
      (.classMem (.cv z)
        (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)) p0055 p0057
  have p0059_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n z) (syn_wb (.imp (.classMem (.cv n)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint
          syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
          syn_cwppstopstep syn_cwppgamma syn_cio syn_cuni
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @g_cbvralv
      (.imp (.classMem (.cv n)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))
      (.imp (.classMem (.cv z)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))
      n z (syn_cnnc) dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      p0059_e00_recanon
  have p0060 :=
    @g_anbi2i
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))
      (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv m)
        (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
      p0059
  have p0061 :=
    @g_anbi2i
      (syn_wa (.classMem (.cv m)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))
      (syn_wa (.classMem (.cv m)
          (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))
      (.classMem (.cv m) (syn_cnnc)) p0060
  have p0062 :=
    @g_biimpri
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
      p0061
  have p0063 := @g_id (.classEq (.cv n) (.cv z))
  have p0064 :=
    @g_eleq1d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z)
      (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
        (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C))
      p0063
  have p0065 := @g_id (.classEq (.cv n) (.cv z))
  have p0066 :=
    @g_breq2d (.classEq (.cv n) (.cv z)) (.cv n) (.cv z) (.cv k) (syn_ckqrel (syn_clefin))
      p0065
  have p0067 :=
    @g_imbi12d (.classEq (.cv n) (.cv z))
      (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
          (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
      (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
          (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)) p0064 p0066
  have p0068_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n z) (syn_wb (.imp (.classMem (.cv n)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint
          syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
          syn_cwppstopstep syn_ctc syn_cio syn_cuni
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0067
  have p0068 :=
    @g_cbvralv
      (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
      (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))
      n z (syn_cnnc) dv_cache_0021 dv_cache_0022 dv_cache_0044 dv_cache_0045
      p0068_e00_recanon
  have p0069 :=
    @g_anbi2i
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))
      (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))
      (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
          (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
      p0068
  have p0070 :=
    @g_anbi2i
      (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
      (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
            (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
        (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))
      (.classMem (.cv k) (syn_cnnc)) p0069
  have p0071 :=
    @g_biimpri
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      p0070
  have p0072 := @g_id (.classEq (.cv y) (.cv r))
  have p0073 :=
    @g_breq2d (.classEq (.cv y) (.cv r)) (.cv y) (.cv r) (syn_ctc C) (syn_clec) p0072
  have p0074 := @g_id (.classEq (.cv y) (.cv r))
  have p0075 :=
    @g_fveq2d (.classEq (.cv y) (.cv r)) (.cv y) (.cv r) (syn_cwppstopstep F C) p0074
  have p0076 :=
    @g_breq2d (.classEq (.cv y) (.cv r)) (syn_cfv (syn_cwppstopstep F C) (.cv y))
      (syn_cfv (syn_cwppstopstep F C) (.cv r)) C (syn_clec) p0075
  have p0077 :=
    @g_imbi12d (.classEq (.cv y) (.cv r)) (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
      (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r))) p0073 p0076
  have p0078_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y r) (syn_wb (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_ctc syn_cio syn_cuni syn_csn syn_clec syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0078 :=
    @g_cbvralv
      (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))
      (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r))))
      y r (syn_cdm (syn_cwppstopstep F C)) dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 p0078_e00_recanon
  have p0079 :=
    @g_biimpri
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
      (syn_wral r (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))
      p0078
  have p0080 :=
    @g_wppstopfixedhitcontrgrowfixdndv
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (syn_wral r (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))
      x y C k m n F (syn_cwppgamma (syn_cwppstopstep F C) C) p dv_cache_0001 dv_cache_0002
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
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
        (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))
      (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C)
        (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)))
      (.imp (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))) (syn_wa
            (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                      (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                        (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                    (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
            (syn_wral r (syn_cdm (syn_cwppstopstep F C))
              (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
                (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))))
        (.neg (.classEq (syn_c0c) (syn_c0c))))
      p0052 p0080
  have p0082 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
                (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F C)
                      (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
        (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z)))))) (syn_wa
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                    (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                      (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
          (syn_wral r (syn_cdm (syn_cwppstopstep F C))
            (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv r))
              (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv r)))))))
      (.neg (.classEq (syn_c0c) (syn_c0c))) p0047 p0081
  have p0083 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (syn_wral y (syn_cdm (syn_cwppstopstep F C))
        (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
      (.neg (.classEq (syn_c0c) (syn_c0c))) p0082
  have p0084 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa
          (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa
            (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k)
              (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)))))))
      (.imp (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
        (.neg (.classEq (syn_c0c) (syn_c0c))))
      p0031 p0083
  have p0085 :=
    @g_ex (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (.imp (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
        (.neg (.classEq (syn_c0c) (syn_c0c))))
      p0084
  have p0086 :=
    @g_rexlimivv
      (syn_wa (syn_wa (.classMem (.cv m)
            (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z) (syn_cwpphit (syn_cwppstopstep F C)
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wa (.classMem (.cv k)
            (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
              (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
          (syn_wral z (syn_cnnc) (.imp (.classMem (.cv z)
                (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                  (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))))))
      (.imp (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
        (.neg (.classEq (syn_c0c) (syn_c0c))))
      m k (syn_cnnc) (syn_cnnc) dv_cache_0028 dv_cache_0070 dv_cache_0071 dv_cache_0032
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

@[expose]
noncomputable def g_wppconcrete6globalnonfixedfromhnshiftndv (y : Var)
    (hyp_wppconcrete6globalnonfixedfromhnshiftndv_1 : Nominal.NPrf (.neg (syn_wbr (syn_chncard
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) :
    Nominal.NPrf
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y))))) :=
  by
  have p0000 := @g_hncardtc6oneeqndv
  have p0001 :=
    @g_breq1i
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_cnc
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_clec) p0000
  have p0002 :=
    @g_mtbir
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wbr (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      hyp_wppconcrete6globalnonfixedfromhnshiftndv_1 p0001
  have p0003 :=
    @g_a1i
      (.neg (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)))
      p0002
  have p0004 :=
    @g_simpl
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)))
      (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0005 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (.cv y))
      p0004
  have p0007 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (.cv y))
      p0004
  have p0008 := @g_hwcardssnc (syn_cvv)
  have p0009 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0007
      p0009
  have p0011 := @g_tlenc1c (.cv y)
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_cnc (syn_c1c))) p0010 p0011
  have p0013 :=
    @g_simpr
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)))
      (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0014 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y)) (syn_cnc (syn_c1c)) (syn_clec) p0013
  have p0015 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_cnc (syn_c1c)))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_cnc (syn_c1c))) p0012 p0014
  have p0021 := @g_n_1cex
  have p0022 := @g_ncelncsi (syn_c1c) p0021
  have p0023 :=
    @g_a1i (.classMem (syn_cnc (syn_c1c)) (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0022
  have p0024 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs)) (.classMem (syn_cnc (syn_c1c)) (syn_cncs)) p0010
      p0023
  have p0025 := @g_tlecg (.cv y) (syn_cnc (syn_c1c))
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_cnc (syn_c1c)) (syn_cncs)))
      (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_cnc (syn_c1c)))
        (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_cnc (syn_c1c)))))
      p0024 p0025
  have p0027 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_cnc (syn_c1c)))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_cnc (syn_c1c)))) p0015 p0026
  have p0029 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_cnc (syn_c1c))) (syn_clec) p0013
  have p0030 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_cnc (syn_c1c))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_cnc (syn_c1c)))) p0027 p0029
  have p0038 := @g_tccl (syn_cnc (syn_c1c))
  have p0039 := Nominal.mp p0022 p0038
  have p0040 :=
    @g_a1i (.classMem (syn_ctc (syn_cnc (syn_c1c))) (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0039
  have p0041 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_cnc (syn_c1c))) (syn_cncs))
      p0010 p0040
  have p0042 := @g_tlecg (.cv y) (syn_ctc (syn_cnc (syn_c1c)))
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cncs))
        (.classMem (syn_ctc (syn_cnc (syn_c1c))) (syn_cncs)))
      (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_cnc (syn_c1c))))
        (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
      p0041 p0042
  have p0044 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_cnc (syn_c1c))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) p0030
      p0043
  have p0046 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_clec) p0013
  have p0047 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) p0044
      p0046
  have p0057 := @g_tccl (syn_ctc (syn_cnc (syn_c1c)))
  have p0058 := Nominal.mp p0039 p0057
  have p0059 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0058
  have p0060 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_cncs)) p0010 p0059
  have p0061 := @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_cncs)))
      (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
        (syn_wbr (syn_ctc (.cv y)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
      p0060 p0061
  have p0063 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
      p0047 p0062
  have p0065 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
      (syn_clec) p0013
  have p0066 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
      p0063 p0065
  have p0078 := @g_tccl (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
  have p0079 := Nominal.mp p0058 p0078
  have p0080 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0079
  have p0081 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_cncs)) p0010 p0080
  have p0082 := @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_cncs)))
      (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
        (syn_wbr (syn_ctc (.cv y)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
      p0081 p0082
  have p0084 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
      p0066 p0083
  have p0086 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_clec) p0013
  have p0087 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
      p0084 p0086
  have p0101 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
  have p0102 := Nominal.mp p0079 p0101
  have p0103 :=
    @g_a1i
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0102
  have p0104 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_cncs))
      p0010 p0103
  have p0105 :=
    @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
  have p0106 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_cncs)))
      (syn_wb (syn_wbr (.cv y) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
        (syn_wbr (syn_ctc (.cv y)) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
      p0104 p0105
  have p0107 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
      p0087 p0106
  have p0109 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_clec)
      p0013
  have p0110 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
      p0107 p0109
  have p0126 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
  have p0127 := Nominal.mp p0102 p0126
  have p0128 :=
    @g_a1i
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
        (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0127
  have p0129 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
        (syn_cncs))
      p0010 p0128
  have p0130 :=
    @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
  have p0131 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cncs))
        (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
          (syn_cncs)))
      (syn_wb (syn_wbr (.cv y) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
        (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))
      p0129 p0130
  have p0132 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
      p0110 p0131
  have p0134 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
      (syn_clec) p0013
  have p0135 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
      p0132 p0134
  have p0153 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
  have p0154 := Nominal.mp p0127 p0153
  have p0155 :=
    @g_a1i
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
        (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0154
  have p0156 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
        (syn_cncs))
      p0010 p0155
  have p0157 :=
    @g_tlecg (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
  have p0158 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
          (syn_cncs)))
      (syn_wb (syn_wbr (.cv y) (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
        (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))))
      p0156 p0157
  have p0159 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))
      p0135 p0158
  have p0161 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
      (syn_clec) p0013
  have p0162 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))
      p0159 p0161
  have p0182 :=
    @g_tccl
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
  have p0183 := Nominal.mp p0154 p0182
  have p0184 :=
    @g_a1i
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
        (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0183
  have p0185 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (.cv y) (syn_cncs))
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
        (syn_cncs))
      p0010 p0184
  have p0186 :=
    @g_tlecg (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
  have p0187 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
          (syn_cncs)))
      (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))
        (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))))
      p0185 p0186
  have p0188 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))))
      p0162 p0187
  have p0190 :=
    @g_breq1d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.cv y) (syn_ctc (.cv y))
      (syn_ctc (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))
      (syn_clec) p0013
  have p0191 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))))
      (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))))
      p0188 p0190
  have p0192 := @g_tcnc1c
  have p0193 := @g_tceq (syn_ctc (syn_cnc (syn_c1c))) (syn_cnc (syn_cpw1 (syn_c1c)))
  have p0194 := Nominal.mp p0192 p0193
  have p0196 := @g_pw1ex (syn_c1c) p0021
  have p0197 := @g_tcnc (syn_cpw1 (syn_c1c)) p0196
  have p0198 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_c1c)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0194 p0197
  have p0199 :=
    @g_tceq (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0200 := Nominal.mp p0198 p0199
  have p0203 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0196
  have p0204 := @g_tcnc (syn_cpw1 (syn_cpw1 (syn_c1c))) p0203
  have p0205 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0200 p0204
  have p0206 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0207 := Nominal.mp p0205 p0206
  have p0211 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0203
  have p0212 := @g_tcnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0211
  have p0213 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0207 p0212
  have p0214 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0215 := Nominal.mp p0213 p0214
  have p0220 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0211
  have p0221 := @g_tcnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0220
  have p0222 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0215
      p0221
  have p0223 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0224 := Nominal.mp p0222 p0223
  have p0230 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0220
  have p0231 :=
    @g_tcnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0230
  have p0232 :=
    @g_eqtri
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0224 p0231
  have p0233 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0234 := Nominal.mp p0232 p0233
  have p0235 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
      (syn_ctc (syn_cnc
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
  have p0236 := Nominal.mp p0234 p0235
  have p0237 :=
    @g_breq2i
      (syn_ctc (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))
      (syn_ctc (syn_ctc (syn_cnc
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (.cv y) (syn_clec) p0236
  have p0238 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0191 p0237
  have p0239 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (.cv y))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0005 p0238
  have p0240 := @g_hncardnc1ndv
  have p0241 := @g_tccl (syn_chncard (syn_c1c))
  have p0242 := Nominal.mp p0240 p0241
  have p0243 := @g_tccl (syn_ctc (syn_chncard (syn_c1c)))
  have p0244 := Nominal.mp p0242 p0243
  have p0245 := @g_tccl (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
  have p0246 := Nominal.mp p0244 p0245
  have p0247 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
  have p0248 := Nominal.mp p0246 p0247
  have p0249 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
  have p0250 := Nominal.mp p0248 p0249
  have p0251 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
  have p0252 := Nominal.mp p0250 p0251
  have p0253 :=
    @g_a1i
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0252
  have p0265 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0230
  have p0266 :=
    @g_ncelncsi
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0265
  have p0267 :=
    @g_tccl
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0268 := Nominal.mp p0266 p0267
  have p0269 :=
    @g_tccl
      (syn_ctc (syn_cnc
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
  have p0270 := Nominal.mp p0268 p0269
  have p0271 :=
    @g_a1i
      (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_cncs))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      p0270
  have p0272 :=
    @g_n_3jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs))
      (.classMem (.cv y) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_cncs))
      p0253 p0010 p0271
  have p0273 :=
    @g_lectr
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (.cv y)
      (syn_ctc (syn_ctc (syn_cnc
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
  have p0274 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_w3a (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_cncs)) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_cnc
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
          (syn_cncs)))
      (.imp (syn_wa (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
        (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      p0272 p0273
  have p0275 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))))
      (syn_wa (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0239 p0274
  have p0276 :=
    @g_ex
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)))
      (.classEq (.cv y) (syn_ctc (.cv y)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0275
  have p0277 :=
    @g_mtod
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)))
      (.classEq (.cv y) (syn_ctc (.cv y)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_cnc (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0003 p0276
  have p0278 := (Nominal.biimpRefl (syn_wne (.cv y) (syn_ctc (.cv y))))
  have p0279 :=
    @g_a1i
      (syn_wb (syn_wne (.cv y) (syn_ctc (.cv y))) (.neg (.classEq (.cv y) (syn_ctc (.cv y)))))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)))
      p0278
  have p0280 :=
    @g_mpbird
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)))
      (syn_wne (.cv y) (syn_ctc (.cv y))) (.neg (.classEq (.cv y) (syn_ctc (.cv y))))
      p0277 p0279
  have p0281 :=
    @g_ex (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (.cv y))
      (syn_wne (.cv y) (syn_ctc (.cv y))) p0280
  have p0282 :=
    @g_rgen
      (.imp (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y))))
      y (syn_chwcards (syn_cvv)) p0281
  exact p0282

@[expose]
noncomputable def g_wppconcrete6rnhwcardsndv :
    Nominal.NPrf (syn_wss (syn_crn (syn_cwppconcrete6fn)) (syn_chwcards (syn_cvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let u : Var := freshVar proofSupport 0
  have p0000 := @g_pwexg (.cv u) (syn_cvv)
  have p0001 := @g_pwexg (syn_cpw (.cv u)) (syn_cvv)
  have p0002 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cpw (.cv u)) (syn_cvv))
      (.classMem (syn_cpw (syn_cpw (.cv u))) (syn_cvv)) p0000 p0001
  have p0003 := @g_hnordexg (syn_cpw (syn_cpw (.cv u)))
  have p0004 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (.cv u))) (syn_cvv))
      (.classMem (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_cvv)) p0002 p0003
  have p0005 := @g_hncardhwcardsndv (syn_chnord (syn_cpw (syn_cpw (.cv u))))
  have p0006 :=
    @g_syl (.classMem (.cv u) (syn_cvv))
      (.classMem (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_cvv))
      (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
        (syn_chwcards (syn_cvv)))
      p0004 p0005
  have p0007 :=
    @g_rgen
      (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
        (syn_chwcards (syn_cvv)))
      u (syn_cvv) p0006
  have p0008 := @g_wppconcrete6rnhwcardsredndv u p0007
  exact p0008

@[expose]
noncomputable def g_wppconcrete6thresholdhwcardsndv :
    Nominal.NPrf
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_chwcards (syn_cvv))) :=
  by
  have p0000 := @g_hncardtc6oneeqndv
  have p0001 := @g_n_1cex
  have p0002 := @g_pw1ex (syn_c1c) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0003
  have p0005 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0004
  have p0006 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0005
  have p0007 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0006
  have p0008 :=
    @g_hncardhwcardsndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_eqeltri
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_chwcards (syn_cvv)) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_wppconcrete6stoppedtchomfullndv (x : Var) :
    Nominal.NPrf
      (syn_wral x (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x)))
          (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_ctc (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  let u : Var := freshVar proofSupport 0
  have p0000 := @g_pwexg (.cv u) (syn_cvv)
  have p0001 := @g_pwexg (syn_cpw (.cv u)) (syn_cvv)
  have p0002 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cpw (.cv u)) (syn_cvv))
      (.classMem (syn_cpw (syn_cpw (.cv u))) (syn_cvv)) p0000 p0001
  have p0003 := @g_hnordexg (syn_cpw (syn_cpw (.cv u)))
  have p0004 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (.cv u))) (syn_cvv))
      (.classMem (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_cvv)) p0002 p0003
  have p0005 := @g_hncardhwcardsndv (syn_chnord (syn_cpw (syn_cpw (.cv u))))
  have p0006 :=
    @g_syl (.classMem (.cv u) (syn_cvv))
      (.classMem (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_cvv))
      (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
        (syn_chwcards (syn_cvv)))
      p0004 p0005
  have p0007 :=
    @g_rgen
      (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
        (syn_chwcards (syn_cvv)))
      u (syn_cvv) p0006
  have p0008 := @g_wppconcrete6rnhwcardsredndv u p0007
  have p0009 := @g_hncardtc6oneeqndv
  have p0010 := @g_n_1cex
  have p0011 := @g_pw1ex (syn_c1c) p0010
  have p0012 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0011
  have p0013 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012
  have p0014 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0013
  have p0015 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0014
  have p0016 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0015
  have p0017 :=
    @g_hncardhwcardsndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_eqeltri
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_chwcards (syn_cvv)) p0009 p0018
  have p0020 := @g_wppconcrete6stoppedtchomndv x p0008 p0019
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

@[expose]
noncomputable def g_wppconcrete6stoppedgammacontrgrowthstagedndv (y : Var)
    (hyp_wppconcrete6stoppedgammacontrgrowthstagedndv_1 : Nominal.NPrf (.neg (syn_wbr
            (syn_chncard
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) :
    Nominal.NPrf
      (.imp (syn_wral y (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.imp
            (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y)) (syn_wbr (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
              (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
                (.cv y))))) (.neg (.classEq (syn_c0c) (syn_c0c)))) :=
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
      ((syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))).fv :=
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
      ((syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))).fv :=
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
      ((syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))).fv :=
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
  have dv_cache_0004 : p ∉ ((syn_cwppconcrete6fn)).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_cwppconcrete6fn)).fv :=
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
  have dv_cache_0006 : y ∉ ((syn_cwppconcrete6fn)).fv :=
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
  have p0000 := @g_wppconcrete6fnfunsndv
  have p0001 := @g_wppconcrete6rnhwcardsndv
  have p0002 := @g_wppconcrete6thresholdhwcardsndv
  have p0003 := @g_wppconcrete6thresholdtclecndv
  have p0004 := @g_wppconcrete6hncard1dmcovndv p
  have p0005 := @g_wppconcrete6stoppedtchomfullndv x
  have p0006 :=
    @g_wppconcrete6globalnonfixedfromhnshiftndv y
      hyp_wppconcrete6stoppedgammacontrgrowthstagedndv_1
  have p0007 :=
    @g_wppstopgammacontrgrowthstagedndv x y
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_cwppconcrete6fn) p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0000 p0001
      p0002 p0003 p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_hnwcutcodeselfnoisoclndv (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
        (.neg (syn_wbr B (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))))) :=
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
      ((Wff.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
          (.neg (syn_wbr B (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)))))).fv :=
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
    @g_id (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
  have p0001 :=
    @g_simpl (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))
  have p0002 := @g_elex B (syn_chwcn A)
  have p0003 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
      (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0001 p0002
  have p0004 := @g_id (.classEq (.cv v) B)
  have p0005 := @g_eleq1d (.classEq (.cv v) B) (.cv v) B (syn_chwcn A) p0004
  have p0007 := @g_fveq2d (.classEq (.cv v) B) (.cv v) B (syn_c2nd) p0004
  have p0008 :=
    @g_eleq2d (.classEq (.cv v) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B)
      (.cv x) p0007
  have p0009 :=
    @g_anbi12d (.classEq (.cv v) B) (.classMem (.cv v) (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) B)) p0005 p0008
  have p0012 := @g_fveq2d (.classEq (.cv v) B) (.cv v) B (syn_c1st) p0004
  have p0015 :=
    @g_jca (.classEq (.cv v) B)
      (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B))
      (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B)) p0012 p0007
  have p0016 :=
    @g_hnwcutcodeeq12ndv x (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v))
      (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
  have p0017 :=
    @g_syl (.classEq (.cv v) B)
      (syn_wa (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B))
        (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B)))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)))
      p0015 p0016
  have p0018 :=
    @g_breq12d (.classEq (.cv v) B) (.cv v) B
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))
      (syn_chwniso A) p0004 p0017
  have p0019 :=
    @g_notbid (.classEq (.cv v) B)
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wbr B (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)))
      p0018
  have p0020 :=
    @g_imbi12d (.classEq (.cv v) B)
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
      (.neg (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.neg (syn_wbr B (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))))
      p0009 p0019
  have p0021 := @g_hnwcutcodeselfnoisondv x v A dv_cache_0001
  have p0022 :=
    @g_vtoclg
      (.imp (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.neg
          (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
        (.neg (syn_wbr B (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)))))
      v B (syn_cvv) dv_cache_0002 dv_cache_0003 p0020 p0021
  have p0023 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
      (.classMem B (syn_cvv))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
        (.neg (syn_wbr B (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)))))
      p0003 p0022
  have p0024 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
      (.neg (syn_wbr B (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))))
      p0000 p0023
  exact p0024


end NFChoice.DirectNominalPrf.WPPReplay

end
