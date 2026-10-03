/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part019`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fpivelfdif (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (d : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_d_x : d ≠ x) (dv_d_y : d ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
        (.classMem (.cv d) (syn_cfdif R A B))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪
      ({ d } : Finset Var)
  let b : Var := freshVar proofSupport 0
  let c : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_d : b ≠ d := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_y : c ≠ y := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_ne_d : c ≠ d := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_p : b ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_b : p ≠ b := Ne.symm fresh_b_ne_p
  have fresh_c_ne_p : c ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_c : p ≠ c := Ne.symm fresh_c_ne_p
  have dv_cache_0001 : Disjoint (A).fv ((Class.cv x)).fv := by
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact dv_A_x))))))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (A).fv from (by exact dv_A_y))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0005 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_d, not_false_eq_true])
  have dv_cache_0006 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
                      (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0007 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact dv_R_x))))))
  have dv_cache_0008 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_x,
          not_false_eq_true])
  have dv_cache_0010 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact dv_R_y))))))
  have dv_cache_0011 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0012 : d ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_y,
          not_false_eq_true])
  have dv_cache_0013 : c ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_R, not_false_eq_true])
  have dv_cache_0014 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_d, not_false_eq_true])
  have dv_cache_0015 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0016 : Disjoint (A).fv (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0017 : Disjoint (A).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint (A).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show c ∉ (A).fv from (by exact fresh_c_not_A))))))
  have dv_cache_0018 : Disjoint (B).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint (B).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (B).fv from (by exact dv_B_x))))))
  have dv_cache_0019 : Disjoint (B).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (show Disjoint (B).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show c ∉ (B).fv from (by exact fresh_c_not_B))))))
  have dv_cache_0020 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0021 : Disjoint ((Class.cv x)).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (show Disjoint ((Class.cv x)).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (c)];
          exact
            (show Disjoint (({ x } : Finset Var)) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ ({ c } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show x ≠ c from (by exact fresh_x_ne_c))))))))
  have dv_cache_0022 : Disjoint ((Class.cv c)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (show Disjoint ((Class.cv c)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ c } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show c ∉ (R).fv from (by exact fresh_c_not_R))))))
  have dv_cache_0023 : Disjoint (A).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (show Disjoint (A).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0024 : Disjoint (A).fv ((syn_copk (.cv x) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (show Disjoint (A).fv ((syn_copk (.cv x) (.cv c))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((A).fv) ((((Class.cv x)).fv) ∪ (((Class.cv c)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show x ∉ (A).fv from (by exact dv_A_x)))))),
                  (show Disjoint ((A).fv) (((Class.cv c)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ c } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show c ∉ (A).fv from (by exact fresh_c_not_A))))))⟩))))
  have dv_cache_0025 : Disjoint (B).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (show Disjoint (B).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0026 : Disjoint (B).fv ((syn_copk (.cv x) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (show Disjoint (B).fv ((syn_copk (.cv x) (.cv c))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((B).fv) ((((Class.cv x)).fv) ∪ (((Class.cv c)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((B).fv) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show x ∉ (B).fv from (by exact dv_B_x)))))),
                  (show Disjoint ((B).fv) (((Class.cv c)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ c } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show c ∉ (B).fv from (by exact fresh_c_not_B))))))⟩))))
  have dv_cache_0027 : Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (show Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv c))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show
              Disjoint (({ p } : Finset Var)) ((((Class.cv x)).fv) ∪ (((Class.cv c)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ p } : Finset Var)) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ ({ x } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show p ≠ x from (by exact fresh_p_ne_x)))))))),
                  (show Disjoint (({ p } : Finset Var)) (((Class.cv c)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) (({ c } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ ({ c } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show p ≠ c from (by exact fresh_p_ne_c))))))))⟩))))
  have dv_cache_0028 : Disjoint ((Class.cv p)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (show Disjoint ((Class.cv p)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ p } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0029 : Disjoint ((syn_copk (.cv x) (.cv c))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (show Disjoint ((syn_copk (.cv x) (.cv c))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((((Class.cv x)).fv) ∪ (((Class.cv c)).fv)) ((R).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (((Class.cv x)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ (R).fv from (by exact dv_R_x)))))),
                  (show Disjoint (((Class.cv c)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ c } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show c ∉ (R).fv from (by exact fresh_c_not_R))))))⟩))))
  have dv_cache_0030 : Disjoint (A).fv ((syn_copk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (show Disjoint (A).fv ((syn_copk (.cv x) (.cv y))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((A).fv) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show x ∉ (A).fv from (by exact dv_A_x)))))),
                  (show Disjoint ((A).fv) (((Class.cv y)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ y } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show y ∉ (A).fv from (by exact dv_A_y))))))⟩))))
  have dv_cache_0031 : Disjoint (B).fv ((syn_copk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (show Disjoint (B).fv ((syn_copk (.cv x) (.cv y))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((B).fv) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((B).fv) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show x ∉ (B).fv from (by exact dv_B_x)))))),
                  (show Disjoint ((B).fv) (((Class.cv y)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ y } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show y ∉ (B).fv from (by exact dv_B_y))))))⟩))))
  have dv_cache_0032 : Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (show Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv y))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show
              Disjoint (({ p } : Finset Var)) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ p } : Finset Var)) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ ({ x } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show p ≠ x from (by exact fresh_p_ne_x)))))))),
                  (show Disjoint (({ p } : Finset Var)) (((Class.cv y)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) (({ y } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ ({ y } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show p ≠ y from (by exact fresh_p_ne_y))))))))⟩))))
  have dv_cache_0033 : Disjoint ((syn_copk (.cv x) (.cv y))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (show Disjoint ((syn_copk (.cv x) (.cv y))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) ((R).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (((Class.cv x)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ (R).fv from (by exact dv_R_x)))))),
                  (show Disjoint (((Class.cv y)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ y } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show y ∉ (R).fv from (by exact dv_R_y))))))⟩))))
  have dv_cache_0034 : p ∉ ((syn_copk (.cv x) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_c, or_false, not_false_eq_true])
  have dv_cache_0035 :
    p ∉
      ((Wff.imp (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (.cv c) (.cv y)))
          (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))
            (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_not_B, fresh_p_not_R, fresh_p_not_A,
          fresh_p_ne_x, fresh_p_ne_c, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0036 : Disjoint (B).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (show Disjoint (B).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (B).fv from (by exact dv_B_y))))))
  have dv_cache_0037 : c ∉ (B).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_B, not_false_eq_true])
  have dv_cache_0038 : c ∉ ((Wff.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_d, fresh_c_not_A, fresh_c_ne_x, fresh_c_ne_y,
          fresh_c_not_R, or_false, not_false_eq_true])
  have dv_cache_0039 :
    c ∉
      ((syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_y, fresh_c_not_B, fresh_c_not_R, fresh_c_not_A,
          fresh_c_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0040 : Disjoint (A).fv ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (show Disjoint (A).fv ((Class.cv b)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ b } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show b ∉ (A).fv from (by exact fresh_b_not_A))))))
  have dv_cache_0041 : Disjoint (B).fv ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (show Disjoint (B).fv ((Class.cv b)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ b } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show b ∉ (B).fv from (by exact fresh_b_not_B))))))
  have dv_cache_0042 : Disjoint ((Class.cv b)).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (show Disjoint ((Class.cv b)).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (b),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (c)];
          exact
            (show Disjoint (({ b } : Finset Var)) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show b ∉ ({ c } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show b ≠ c from (by exact fresh_b_ne_c))))))))
  have dv_cache_0043 : Disjoint ((Class.cv b)).fv (R).fv :=
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
      (show Disjoint ((Class.cv b)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ b } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show b ∉ (R).fv from (by exact fresh_b_not_R))))))
  have dv_cache_0044 : Disjoint (A).fv ((syn_copk (.cv b) (.cv c))).fv :=
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
      (show Disjoint (A).fv ((syn_copk (.cv b) (.cv c))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((A).fv) ((((Class.cv b)).fv) ∪ (((Class.cv c)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv b)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ b } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show b ∉ (A).fv from (by exact fresh_b_not_A)))))),
                  (show Disjoint ((A).fv) (((Class.cv c)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ c } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show c ∉ (A).fv from (by exact fresh_c_not_A))))))⟩))))
  have dv_cache_0045 : Disjoint (B).fv ((syn_copk (.cv b) (.cv c))).fv :=
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
      (show Disjoint (B).fv ((syn_copk (.cv b) (.cv c))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((B).fv) ((((Class.cv b)).fv) ∪ (((Class.cv c)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((B).fv) (((Class.cv b)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ b } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show b ∉ (B).fv from (by exact fresh_b_not_B)))))),
                  (show Disjoint ((B).fv) (((Class.cv c)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ c } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show c ∉ (B).fv from (by exact fresh_c_not_B))))))⟩))))
  have dv_cache_0046 : Disjoint ((Class.cv p)).fv ((syn_copk (.cv b) (.cv c))).fv :=
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
      (show Disjoint ((Class.cv p)).fv ((syn_copk (.cv b) (.cv c))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show
              Disjoint (({ p } : Finset Var)) ((((Class.cv b)).fv) ∪ (((Class.cv c)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ p } : Finset Var)) (((Class.cv b)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) (({ b } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ ({ b } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show p ≠ b from (by exact fresh_p_ne_b)))))))),
                  (show Disjoint (({ p } : Finset Var)) (((Class.cv c)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) (({ c } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ ({ c } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show p ≠ c from (by exact fresh_p_ne_c))))))))⟩))))
  have dv_cache_0047 : Disjoint ((syn_copk (.cv b) (.cv c))).fv (R).fv :=
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
      (show Disjoint ((syn_copk (.cv b) (.cv c))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((((Class.cv b)).fv) ∪ (((Class.cv c)).fv)) ((R).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (((Class.cv b)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ b } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show b ∉ (R).fv from (by exact fresh_b_not_R)))))),
                  (show Disjoint (((Class.cv c)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ c } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show c ∉ (R).fv from (by exact fresh_c_not_R))))))⟩))))
  have dv_cache_0048 : p ∉ ((syn_copk (.cv b) (.cv c))).fv :=
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
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_b, fresh_p_ne_c, or_false, not_false_eq_true])
  have dv_cache_0049 :
    p ∉
      ((Wff.imp (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B)
                (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
          (.classEq (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c)))
            (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_not_B, fresh_p_not_R, fresh_p_not_A,
          fresh_p_ne_x, fresh_p_ne_b, fresh_p_ne_c, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0050 :
    c ∉
      ((syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x)))).fv :=
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
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_y, fresh_c_not_B, fresh_c_not_R, fresh_c_not_A,
          fresh_c_ne_x, fresh_c_ne_b, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0051 : b ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0052 : b ∉ (B).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0053 :
    b ∉ ((syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_B, fresh_b_ne_d,
          fresh_b_not_A, fresh_b_ne_x, fresh_b_ne_c, fresh_b_not_R, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0054 :
    b ∉
      ((syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))).fv :=
    by
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_not_B, fresh_b_not_R, fresh_b_not_A,
          fresh_b_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0055 : b ∉ (A).fv :=
    by
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
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0056 : d ∉ (B).fv :=
    by
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
        simp only [dv_B_d, not_false_eq_true])
  have dv_cache_0057 : b ∉ (R).fv :=
    by
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
        simp only [fresh_b_not_R, not_false_eq_true])
  have dv_cache_0058 : d ≠ b :=
    by
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
    exact (show d ≠ b from (by exact fresh_d_ne_b))
  have dv_cache_0059 : d ≠ c :=
    by
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
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0060 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have p0000 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      p0000
  have p0002 :=
    @g_simpll (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
          (syn_wbr (.cv d) R (.cv c))))
  have p0003 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) A) p0001 p0002
  have p0004 :=
    @g_a1i
      (.imp (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) p0003
  have p0005 :=
    @g_simp3 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0006 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classEq (.cv c) (.cv y))
  have p0007 :=
    @g_simp1 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0008 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr R (syn_cwe) A) p0006 p0007
  have p0010 :=
    @g_simp2 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0011 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv x) B) p0006 p0010
  have p0012 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classEq (.cv c) (.cv y))
  have p0015 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv y) B) p0006 p0005
  have p0016 :=
    @g_eqeltrd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (.cv c) (.cv y) B p0012 p0015
  have p0017 :=
    @g_jca
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (.classMem (.cv x) B) (.classMem (.cv c) B) p0011 p0016
  have p0018 :=
    @g_jca
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv c) B)) p0008
      p0017
  have p0019 :=
    @g_fdminvalpfpivred A B (.cv x) (.cv c) R dv_cache_0016 dv_cache_0001 dv_cache_0017
      dv_cache_0003 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0007
      dv_cache_0022
  have p0020 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv c) B)))
      (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))
        (syn_cfpiv R A (.cv x) (.cv c)))
      p0018 p0019
  have p0021 :=
    @g_eqcomd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfpiv R A (.cv x) (.cv c))
      p0020
  have p0022 := @g_opkex (.cv x) (.cv c)
  have p0023 :=
    @g_simpl (.classEq (.cv p) (syn_copk (.cv x) (.cv c)))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
  have p0024 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv x) (.cv c)) R dv_cache_0016 dv_cache_0023
      dv_cache_0024 dv_cache_0003 dv_cache_0025 dv_cache_0026 dv_cache_0020 dv_cache_0027
      dv_cache_0028 dv_cache_0029
  have p0025 :=
    @g_syl
      (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv c) (.cv y))))
      (.classEq (.cv p) (syn_copk (.cv x) (.cv c)))
      (.classEq (syn_cfdminvalp R A B (.cv p))
        (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))))
      p0023 p0024
  have p0026 :=
    @g_eqcomd
      (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv c) (.cv y))))
      (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))
      p0025
  have p0028 :=
    @g_simpr (.classEq (.cv p) (syn_copk (.cv x) (.cv c)))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
  have p0030 :=
    @g_opkeq2d
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (.cv c) (.cv y) (.cv x) p0012
  have p0031 :=
    @g_syl
      (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv c) (.cv y))))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (.classEq (syn_copk (.cv x) (.cv c)) (syn_copk (.cv x) (.cv y))) p0028 p0030
  have p0032 :=
    @g_eqtrd
      (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv c) (.cv y))))
      (.cv p) (syn_copk (.cv x) (.cv c)) (syn_copk (.cv x) (.cv y)) p0023 p0031
  have p0033 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv x) (.cv y)) R dv_cache_0016 dv_cache_0023
      dv_cache_0030 dv_cache_0003 dv_cache_0025 dv_cache_0031 dv_cache_0020 dv_cache_0032
      dv_cache_0028 dv_cache_0033
  have p0034 :=
    @g_syl
      (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv c) (.cv y))))
      (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
      (.classEq (syn_cfdminvalp R A B (.cv p))
        (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))))
      p0032 p0033
  have p0035 :=
    @g_eqtrd
      (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv c) (.cv y))))
      (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfdminvalp R A B (.cv p))
      (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) p0026 p0034
  have p0036 :=
    @g_ex (.classEq (.cv p) (syn_copk (.cv x) (.cv c)))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))
        (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))))
      p0035
  have p0037 :=
    @g_vtocleg
      (.imp (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv c) (.cv y)))
        (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))
          (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))))
      p (syn_copk (.cv x) (.cv c)) (syn_cvv) dv_cache_0034 dv_cache_0035 p0036
  have p0038 := Nominal.mp p0022 p0037
  have p0048 :=
    @g_jca
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0011 p0015
  have p0049 :=
    @g_jca
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0008
      p0048
  have p0050 :=
    @g_fdminvalpfpivred A B (.cv x) (.cv y) R dv_cache_0016 dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0018 dv_cache_0036 dv_cache_0020 dv_cache_0006 dv_cache_0007
      dv_cache_0010
  have p0051 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))
        (syn_cfpiv R A (.cv x) (.cv y)))
      p0049 p0050
  have p0052 :=
    @g_n_3eqtrd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_cfpiv R A (.cv x) (.cv c)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))
      (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y))
      p0021 p0038 p0051
  have p0053 :=
    @g_eleq2d
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv c) (.cv y)))
      (syn_cfpiv R A (.cv x) (.cv c)) (syn_cfpiv R A (.cv x) (.cv y)) (.cv d) p0052
  have p0054 :=
    @g_rspcedv
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) c (.cv y) B dv_cache_0011
      dv_cache_0037 dv_cache_0038 dv_cache_0039 p0005 p0053
  have p0056 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv b) (.cv x)))
      (.classMem (.cv c) B)
  have p0057 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classEq (.cv b) (.cv x))
  have p0059 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv b) (.cv x)))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr R (syn_cwe) A) p0057 p0007
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv b) (.cv x)))
      (syn_wbr R (syn_cwe) A) p0056 p0059
  have p0062 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classEq (.cv b) (.cv x))
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv b) (.cv x)))
      (.classEq (.cv b) (.cv x)) p0056 p0062
  have p0067 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv b) (.cv x)))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv x) B) p0057 p0010
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv b) (.cv x)))
      (.classMem (.cv x) B) p0056 p0067
  have p0069 :=
    @g_eqeltrd
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (.cv b) (.cv x) B p0063 p0068
  have p0070 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv b) (.cv x)))
      (.classMem (.cv c) B)
  have p0071 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (.classMem (.cv b) B) (.classMem (.cv c) B) p0069 p0070
  have p0072 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv b) B) (.classMem (.cv c) B)) p0060
      p0071
  have p0073 :=
    @g_fdminvalpfpivred A B (.cv b) (.cv c) R dv_cache_0016 dv_cache_0040 dv_cache_0017
      dv_cache_0003 dv_cache_0041 dv_cache_0019 dv_cache_0020 dv_cache_0042 dv_cache_0043
      dv_cache_0022
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv b) B) (.classMem (.cv c) B)))
      (.classEq (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c)))
        (syn_cfpiv R A (.cv b) (.cv c)))
      p0072 p0073
  have p0075 :=
    @g_eqcomd
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfpiv R A (.cv b) (.cv c))
      p0074
  have p0076 := @g_opkex (.cv b) (.cv c)
  have p0077 :=
    @g_simpl (.classEq (.cv p) (syn_copk (.cv b) (.cv c)))
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
  have p0078 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv b) (.cv c)) R dv_cache_0016 dv_cache_0023
      dv_cache_0044 dv_cache_0003 dv_cache_0025 dv_cache_0045 dv_cache_0020 dv_cache_0046
      dv_cache_0028 dv_cache_0047
  have p0079 :=
    @g_syl
      (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)))
      (.classEq (.cv p) (syn_copk (.cv b) (.cv c)))
      (.classEq (syn_cfdminvalp R A B (.cv p))
        (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))))
      p0077 p0078
  have p0080 :=
    @g_eqcomd
      (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)))
      (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c)))
      p0079
  have p0082 :=
    @g_simpr (.classEq (.cv p) (syn_copk (.cv b) (.cv c)))
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
  have p0086 :=
    @g_opkeq1d
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (.cv b) (.cv x) (.cv c) p0063
  have p0087 :=
    @g_syl
      (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)))
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (.classEq (syn_copk (.cv b) (.cv c)) (syn_copk (.cv x) (.cv c))) p0082 p0086
  have p0088 :=
    @g_eqtrd
      (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)))
      (.cv p) (syn_copk (.cv b) (.cv c)) (syn_copk (.cv x) (.cv c)) p0077 p0087
  have p0090 :=
    @g_syl
      (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)))
      (.classEq (.cv p) (syn_copk (.cv x) (.cv c)))
      (.classEq (syn_cfdminvalp R A B (.cv p))
        (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))))
      p0088 p0024
  have p0091 :=
    @g_eqtrd
      (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)))
      (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfdminvalp R A B (.cv p))
      (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) p0080 p0090
  have p0092 :=
    @g_ex (.classEq (.cv p) (syn_copk (.cv b) (.cv c)))
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (.classEq (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c)))
        (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))))
      p0091
  have p0093 :=
    @g_vtocleg
      (.imp (syn_wa (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
        (.classEq (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c)))
          (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))))
      p (syn_copk (.cv b) (.cv c)) (syn_cvv) dv_cache_0048 dv_cache_0049 p0092
  have p0094 := Nominal.mp p0076 p0093
  have p0106 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (.classMem (.cv x) B) (.classMem (.cv c) B) p0068 p0070
  have p0107 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv c) B)) p0060
      p0106
  have p0109 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv c) B)))
      (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))
        (syn_cfpiv R A (.cv x) (.cv c)))
      p0107 p0019
  have p0110 :=
    @g_n_3eqtrd
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_cfpiv R A (.cv b) (.cv c)) (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c)))
      (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfpiv R A (.cv x) (.cv c))
      p0075 p0094 p0109
  have p0111 :=
    @g_eleq2d
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
      (syn_cfpiv R A (.cv b) (.cv c)) (syn_cfpiv R A (.cv x) (.cv c)) (.cv d) p0110
  have p0112 :=
    @g_rexbidva
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (.cv b) (.cv x)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c))) c B dv_cache_0050 p0111
  have p0113 :=
    @g_rspcedv
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c))))
      (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c)))) b (.cv x) B
      dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 p0010 p0112
  have p0114 :=
    @g_syld (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c))))
      (syn_wrex b B (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c)))))
      p0054 p0113
  have p0115 :=
    @g_jcad (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A)
      (syn_wrex b B (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c)))))
      p0004 p0114
  have p0116 :=
    @g_elfdif b c A B R d dv_cache_0016 dv_cache_0003 dv_cache_0005 dv_cache_0055
      dv_cache_0004 dv_cache_0020 dv_cache_0056 dv_cache_0052 dv_cache_0037 dv_cache_0014
      dv_cache_0057 dv_cache_0013 dv_cache_0058 dv_cache_0059 dv_cache_0060
  have p0117 :=
    @g_biimpri (.classMem (.cv d) (syn_cfdif R A B))
      (syn_wa (.classMem (.cv d) A)
        (syn_wrex b B (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c))))))
      p0116
  have p0118 :=
    @g_syl6 (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (.classMem (.cv d) A)
        (syn_wrex b B (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c))))))
      (.classMem (.cv d) (syn_cfdif R A B)) p0115 p0117
  have p0119 :=
    @g_imp (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfdif R A B)) p0118
  exact p0119


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part020`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fdrowsep (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (d : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_d_x : d ≠ x) (dv_d_y : d ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
        (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪
      ({ d } : Finset Var)
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_c_ne_y : c ≠ y := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_ne_d : c ≠ d := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : Disjoint (A).fv ((Class.cv x)).fv := by
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact dv_A_x))))))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (A).fv from (by exact dv_A_y))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0005 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_d, not_false_eq_true])
  have dv_cache_0006 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
                      (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0007 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact dv_R_x))))))
  have dv_cache_0008 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_x,
          not_false_eq_true])
  have dv_cache_0010 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact dv_R_y))))))
  have dv_cache_0011 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0012 : d ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_y,
          not_false_eq_true])
  have dv_cache_0013 : c ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_R, not_false_eq_true])
  have dv_cache_0014 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_d, not_false_eq_true])
  have dv_cache_0015 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0016 : Disjoint (A).fv (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0017 : Disjoint (A).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint (A).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (A).fv from (by exact dv_A_d))))))
  have dv_cache_0018 : Disjoint (B).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint (B).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (B).fv from (by exact dv_B_x))))))
  have dv_cache_0019 : Disjoint (B).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (show Disjoint (B).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (B).fv from (by exact dv_B_d))))))
  have dv_cache_0020 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0021 : Disjoint ((Class.cv x)).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (show Disjoint ((Class.cv x)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)];
          exact
            (show Disjoint (({ x } : Finset Var)) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ ({ d } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show x ≠ d from (by exact Ne.symm dv_d_x))))))))
  have dv_cache_0022 : Disjoint ((Class.cv d)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (show Disjoint ((Class.cv d)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ d } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show d ∉ (R).fv from (by exact dv_R_d))))))
  have dv_cache_0023 : x ∉ (A).fv :=
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
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0024 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0025 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_d, not_false_eq_true])
  have dv_cache_0026 : x ∉ (B).fv :=
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
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0027 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0028 : x ∉ (R).fv :=
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
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0029 : y ∉ (R).fv :=
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
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0030 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show d ≠ x from (by exact dv_d_x))
  have dv_cache_0031 : d ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show d ≠ y from (by exact dv_d_y))
  have dv_cache_0032 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0033 : Disjoint (B).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (show Disjoint (B).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (B).fv from (by exact dv_B_y))))))
  have dv_cache_0034 : Disjoint ((Class.cv y)).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (show Disjoint ((Class.cv y)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (y),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)];
          exact
            (show Disjoint (({ y } : Finset Var)) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ ({ d } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show y ≠ d from (by exact Ne.symm dv_d_y))))))))
  have p0000 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0001 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0002 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      p0001
  have p0003 :=
    @g_simplr (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
          (syn_wbr (.cv d) R (.cv c))))
  have p0004 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) p0002 p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) p0000 p0004
  have p0006 := @g_sep2valJp (.cv x) (.cv y) d dv_cache_0006 dv_cache_0009 dv_cache_0012
  have p0007 := @g_xor (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d))
  have p0008 :=
    @g_bicomi (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d))))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv d)) (.neg (.classMem (.cv y) (.cv d))))
        (syn_wa (.classMem (.cv y) (.cv d)) (.neg (.classMem (.cv x) (.cv d)))))
      p0007
  have p0009 :=
    @g_bitri (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv d)) (.neg (.classMem (.cv y) (.cv d))))
        (syn_wa (.classMem (.cv y) (.cv d)) (.neg (.classMem (.cv x) (.cv d)))))
      (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) p0006 p0008
  have p0010 :=
    @g_biimpi (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) p0009
  have p0011 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) p0005 p0010
  have p0012 :=
    @g_elfdrowg A B (.cv x) (.cv d) R dv_cache_0016 dv_cache_0001 dv_cache_0017
      dv_cache_0003 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0007
      dv_cache_0022
  have p0013 :=
    @g_a1i
      (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x)))
        (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv x) (.cv d))))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      p0012
  have p0014 :=
    @g_fpivelfdif x y A B R d dv_cache_0016 dv_cache_0003 dv_cache_0005 dv_cache_0023
      dv_cache_0024 dv_cache_0020 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0014
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
  have p0015 :=
    @g_biantrurd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv x) (.cv d)) p0014
  have p0016 :=
    @g_bicomd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv x) (.cv d))
      (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv x) (.cv d))) p0015
  have p0017 :=
    @g_bitrd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv d) (syn_cfdrow R A B (.cv x)))
      (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv x) (.cv d)))
      (.classMem (.cv x) (.cv d)) p0013 p0016
  have p0018 :=
    @g_elfdrowg A B (.cv y) (.cv d) R dv_cache_0016 dv_cache_0002 dv_cache_0017
      dv_cache_0003 dv_cache_0033 dv_cache_0019 dv_cache_0020 dv_cache_0034 dv_cache_0010
      dv_cache_0022
  have p0019 :=
    @g_a1i
      (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv y)))
        (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv y) (.cv d))))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      p0018
  have p0021 :=
    @g_biantrurd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv y) (.cv d)) p0014
  have p0022 :=
    @g_bicomd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv y) (.cv d))
      (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv y) (.cv d))) p0021
  have p0023 :=
    @g_bitrd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv d) (syn_cfdrow R A B (.cv y)))
      (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv y) (.cv d)))
      (.classMem (.cv y) (.cv d)) p0019 p0022
  have p0024 :=
    @g_bibi12d
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.classMem (.cv d) (syn_cfdrow R A B (.cv x))) (.classMem (.cv x) (.cv d))
      (.classMem (.cv d) (syn_cfdrow R A B (.cv y))) (.classMem (.cv y) (.cv d)) p0017
      p0023
  have p0025 :=
    @g_notbid
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x)))
        (.classMem (.cv d) (syn_cfdrow R A B (.cv y))))
      (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d))) p0024
  have p0026 :=
    @g_mpbird
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.neg (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x)))
          (.classMem (.cv d) (syn_cfdrow R A B (.cv y)))))
      (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) p0011 p0025
  have p0027 := @g_eleq2 (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)) (.cv d)
  have p0028 :=
    @g_necon3bi
      (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x)))
        (.classMem (.cv d) (syn_cfdrow R A B (.cv y))))
      (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)) p0027
  have p0029 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (.neg (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x)))
          (.classMem (.cv d) (syn_cfdrow R A B (.cv y)))))
      (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0026 p0028
  exact p0029

@[expose]
noncomputable def g_sep2ex2 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classMem (syn_csep2 (.cv x) (.cv y)) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let c : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_y : c ≠ y := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_b : c ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_c : b ≠ c := Ne.symm fresh_c_ne_b
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv := by
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
                      (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0002 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0003 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0004 : c ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_b, not_false_eq_true])
  have dv_cache_0005 : c ∉ ((Wff.classMem (.cv x) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_b, or_false, not_false_eq_true])
  have dv_cache_0006 : c ∉ ((Wff.classMem (.cv y) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_b, or_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((syn_csep2 (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, or_false, not_false_eq_true])
  have dv_cache_0008 :
    b ∉
      ((syn_csymdif (.cab c (.classMem (.cv x) (.cv c)))
          (.cab c (.classMem (.cv y) (.cv c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_c, fresh_b_ne_y, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0009 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0010 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have p0000 := @g_sep2valJp (.cv x) (.cv y) b dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_elsymdif (.cv b) (.cab c (.classMem (.cv x) (.cv c)))
      (.cab c (.classMem (.cv y) (.cv c)))
  have p0002 := @g_vex b
  have p0003 := @g_eleq2 (.cv c) (.cv b) (.cv x)
  have p0004 :=
    @g_elab (.classMem (.cv x) (.cv c)) (.classMem (.cv x) (.cv b)) c (.cv b)
      dv_cache_0004 dv_cache_0005 p0002 p0003
  have p0006 := @g_eleq2 (.cv c) (.cv b) (.cv y)
  have p0007 :=
    @g_elab (.classMem (.cv y) (.cv c)) (.classMem (.cv y) (.cv b)) c (.cv b)
      dv_cache_0004 dv_cache_0006 p0002 p0006
  have p0008 :=
    @g_bibi12i (.classMem (.cv b) (.cab c (.classMem (.cv x) (.cv c))))
      (.classMem (.cv x) (.cv b)) (.classMem (.cv b) (.cab c (.classMem (.cv y) (.cv c))))
      (.classMem (.cv y) (.cv b)) p0004 p0007
  have p0009 :=
    @g_notbii
      (syn_wb (.classMem (.cv b) (.cab c (.classMem (.cv x) (.cv c))))
        (.classMem (.cv b) (.cab c (.classMem (.cv y) (.cv c)))))
      (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))) p0008
  have p0010 :=
    @g_bitri
      (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c)))
          (.cab c (.classMem (.cv y) (.cv c)))))
      (.neg (syn_wb (.classMem (.cv b) (.cab c (.classMem (.cv x) (.cv c))))
          (.classMem (.cv b) (.cab c (.classMem (.cv y) (.cv c))))))
      (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))) p0001 p0009
  have p0011 := @g_xor (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))
  have p0012 :=
    @g_bitri
      (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c)))
          (.cab c (.classMem (.cv y) (.cv c)))))
      (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b))))
        (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b)))))
      p0010 p0011
  have p0013 :=
    @g_bicomi
      (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c)))
          (.cab c (.classMem (.cv y) (.cv c)))))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b))))
        (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b)))))
      p0012
  have p0014 :=
    @g_bitri (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b))))
        (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b)))))
      (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c)))
          (.cab c (.classMem (.cv y) (.cv c)))))
      p0000 p0013
  have p0015 :=
    @g_eqabi
      (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c)))
          (.cab c (.classMem (.cv y) (.cv c)))))
      b (syn_csep2 (.cv x) (.cv y)) dv_cache_0007 p0014
  have p0016 :=
    @g_abid2 b
      (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))
      dv_cache_0008
  have p0017 :=
    @g_eqtri (syn_csep2 (.cv x) (.cv y))
      (.cab b (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c)))
            (.cab c (.classMem (.cv y) (.cv c))))))
      (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))
      p0015 p0016
  have p0018 := @g_setswithex c (.cv x) dv_cache_0009
  have p0019 := @g_setswithex c (.cv y) dv_cache_0010
  have p0020 :=
    @g_symdifex (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c)))
      p0018 p0019
  have p0021 :=
    @g_eqeltri (syn_csep2 (.cv x) (.cv y))
      (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))
      (syn_cvv) p0017 p0020
  exact p0021


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fpivex (x : Var) (y : Var) (A : Class) (R : Class) (b : Var) (d : Var)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_b : b ∉ A.fv) (dv_A_d : d ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (_dv_R_b : b ∉ R.fv) (dv_R_d : d ∉ R.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_b_d : b ≠ d) (dv_b_x : b ≠ x)
    (dv_b_y : b ≠ y) (dv_d_x : d ≠ x) (dv_d_y : d ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
        (syn_wrex d A (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ R.fv ∪ ({ b } : Finset Var) ∪
      ({ d } : Finset Var)
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_c_ne_y : c ≠ y := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_ne_b : c ≠ b := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_c : b ≠ c := Ne.symm fresh_c_ne_b
  have fresh_c_ne_d : c ≠ d := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have dv_cache_0001 : b ∉ ((syn_csep2 (.cv x) (.cv y))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_b_x, dv_b_y, or_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_b, not_false_eq_true])
  have dv_cache_0004 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_d, not_false_eq_true])
  have dv_cache_0005 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0006 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_d, not_false_eq_true])
  have dv_cache_0007 : c ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_R, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Wff.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union,
          Finset.mem_singleton, dv_b_d, dv_b_x, dv_b_y, or_false, not_false_eq_true])
  have dv_cache_0009 :
    d ∉
      ((syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_R_d, dv_A_d, (Ne.symm dv_b_d),
          dv_d_x, dv_d_y, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0010 :
    c ∉
      ((syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_not_R, fresh_c_not_A,
          fresh_c_ne_b, fresh_c_ne_x, fresh_c_ne_y, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Wff.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_b_d), dv_d_x, dv_d_y, or_false,
          not_false_eq_true])
  have dv_cache_0012 : c ∉ ((Wff.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_x, fresh_c_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0013 : b ∉ ((Wff.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_c, dv_b_x, dv_b_y, or_false,
          not_false_eq_true])
  have dv_cache_0014 : b ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show b ≠ d from (by exact dv_b_d))
  have dv_cache_0015 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0016 : d ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0017 : Disjoint (A).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact dv_A_x))))))
  have dv_cache_0018 : Disjoint (A).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint (A).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (A).fv from (by exact dv_A_y))))))
  have dv_cache_0019 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0020 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
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
                      (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0021 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact dv_R_x))))))
  have dv_cache_0022 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0023 : d ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_x,
          not_false_eq_true])
  have dv_cache_0024 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact dv_R_y))))))
  have dv_cache_0025 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0026 : d ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_y,
          not_false_eq_true])
  have dv_cache_0027 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have p0000 := @g_abid2 b (syn_csep2 (.cv x) (.cv y)) dv_cache_0001
  have p0001 := @g_sep2ex2 x y dv_cache_0002
  have p0002 :=
    @g_eqeltri (.cab b (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
      (syn_csep2 (.cv x) (.cv y)) (syn_cvv) p0000 p0001
  have p0003 := @g_eleq1 (.cv b) (.cv d) (syn_csep2 (.cv x) (.cv y))
  have p0004 := @g_eleq1 (.cv b) (.cv c) (syn_csep2 (.cv x) (.cv y))
  have p0005 :=
    @g_simpl (syn_wbr R (syn_cwe) A)
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0006 :=
    @g_simpr (syn_wbr R (syn_cwe) A)
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0007_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq b d) (syn_wb (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))
          (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csep2 syn_wo syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq b c) (syn_wb (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))
          (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csep2 syn_wo syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0007 :=
    @g_weds
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) b d c A R dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 p0002 p0007_e01_recanon p0007_e02_recanon p0005 p0006
  have p0008 :=
    @g_simpr
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (.classMem (.cv d) A)
  have p0009 :=
    @g_a1d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A))
      (.classMem (.cv d) A)
      (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))))
      p0008
  have p0010 :=
    @g_simpl (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
          (syn_wbr (.cv d) R (.cv c))))
  have p0011 :=
    @g_a1i
      (.imp (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A
            (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))))
        (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A))
      p0010
  have p0012 :=
    @g_jcad
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A))
      (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) p0009 p0011
  have p0013 :=
    @g_simpr (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
          (syn_wbr (.cv d) R (.cv c))))
  have p0014 :=
    @g_a1i
      (.imp (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A
            (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A))
      p0013
  have p0015 :=
    @g_jcad
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A))
      (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))))
      (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
          (syn_wbr (.cv d) R (.cv c))))
      p0012 p0014
  have p0016 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0005 dv_cache_0004 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0007 dv_cache_0006 dv_cache_0027
  have p0017 :=
    @g_biimpri (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      p0016
  have p0018 :=
    @g_syl6
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A)
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A))
      (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) p0015 p0017
  have p0019 :=
    @g_reximdva
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) d A dv_cache_0009 p0018
  have p0020 :=
    @g_mpd
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (syn_wrex d A (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A
            (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
              (syn_wbr (.cv d) R (.cv c))))))
      (syn_wrex d A (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) p0007 p0019
  exact p0020

@[expose]
noncomputable def g_fdrowdiff (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (b : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_B_b : b ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
        (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪
      ({ b } : Finset Var)
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_d_ne_y : d ≠ y := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_ne_b : d ≠ b := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_d : b ≠ d := Ne.symm fresh_d_ne_b
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0002 : b ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_b, not_false_eq_true])
  have dv_cache_0003 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0006 : b ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_b, not_false_eq_true])
  have dv_cache_0007 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0009 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0010 : b ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show b ≠ d from (by exact fresh_b_ne_d))
  have dv_cache_0011 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show b ≠ x from (by exact dv_b_x))
  have dv_cache_0012 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show b ≠ y from (by exact dv_b_y))
  have dv_cache_0013 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0014 : d ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show d ≠ y from (by exact fresh_d_ne_y))
  have dv_cache_0015 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0016 : Disjoint (A).fv (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0017 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0018 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0019 : x ∉ (B).fv :=
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
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0020 : y ∉ (B).fv :=
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
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0021 :
    d ∉ ((syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_ne_x, fresh_d_not_R,
          fresh_d_ne_y, or_false, not_false_eq_true])
  have dv_cache_0022 :
    d ∉
      ((syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_y, fresh_d_not_B,
          fresh_d_not_R, fresh_d_not_A, fresh_d_ne_x, fresh_d_ne_b,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0001 :=
    @g_simp1 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0002 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr R (syn_cwe) A) p0000 p0001
  have p0003 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0004 :=
    @g_jca
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (syn_wbr R (syn_cwe) A)
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) p0002 p0003
  have p0005 :=
    @g_fpivex x y A R b d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0006 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (syn_wrex d A (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) p0004 p0005
  have p0007 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (.classMem (.cv d) A)
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) p0007
      p0000
  have p0010 :=
    @g_fdrowsep x y A B R d dv_cache_0016 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0011 :=
    @g_ex (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0010
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.imp (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
        (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      p0009 p0011
  have p0013 :=
    @g_rexlimdva
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) d A dv_cache_0021
      dv_cache_0022 p0012
  have p0014 :=
    @g_mpd
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      (syn_wrex d A (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0006 p0013
  exact p0014

@[expose]
noncomputable def g_fdroweqnosep (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (b : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_b : b ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
        (.neg (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_b, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_b, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0010 : b ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_b, not_false_eq_true])
  have dv_cache_0011 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0012 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0013 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show b ≠ x from (by exact dv_b_x))
  have dv_cache_0014 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show b ≠ y from (by exact dv_b_y))
  have dv_cache_0015 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0001 := @g_nne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))
  have p0002 :=
    @g_bicomi (.neg (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0001
  have p0003 :=
    @g_sylib
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
      (.neg (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) p0000 p0002
  have p0004 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0005 :=
    @g_fdrowdiff x y A B R b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0006 :=
    @g_ex (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
      (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0005
  have p0007 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.imp (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
        (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      p0004 p0006
  have p0008 :=
    @g_mtod
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
      (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0003 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fdroweqmem (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (_dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (_dv_C_R : Disjoint C.fv R.fv) (_dv_C_x : x ∉ C.fv)
    (_dv_C_y : y ∉ C.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa
            (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
            (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
        (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let b : Var := freshVar proofSupport 0
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0010 : b ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0012 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0013 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0014 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0015 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0016 : b ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_C, not_false_eq_true])
  have dv_cache_0017 : b ∉ ((Wff.classMem C (syn_csep2 (.cv x) (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_C, fresh_b_ne_x, fresh_b_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0018 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
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
                      (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0019 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0020 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0021 :
    b ∉
      ((syn_wb (.classMem C (syn_csep2 (.cv x) (.cv y)))
          (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_singleton,
          fresh_b_not_C, fresh_b_ne_x, fresh_b_ne_y, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.classMem C A)
  have p0001 :=
    @g_fdroweqnosep x y A B R b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.neg (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) p0000 p0001
  have p0003 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.classMem C A)
  have p0004 := @g_eleq1 (.cv b) C (syn_csep2 (.cv x) (.cv y))
  have p0005 :=
    @g_rspcev (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))
      (.classMem C (syn_csep2 (.cv x) (.cv y))) b C A dv_cache_0016 dv_cache_0003
      dv_cache_0017 p0004
  have p0006 :=
    @g_ex (.classMem C A) (.classMem C (syn_csep2 (.cv x) (.cv y)))
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) p0005
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
      (.classMem C A)
      (.imp (.classMem C (syn_csep2 (.cv x) (.cv y)))
        (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))
      p0003 p0006
  have p0008 :=
    @g_mtod
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
      (.classMem C (syn_csep2 (.cv x) (.cv y)))
      (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) p0002 p0007
  have p0010 := @g_elex C A
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
      (.classMem C A) (.classMem C (syn_cvv)) p0003 p0010
  have p0013 := @g_eleq2 (.cv b) C (.cv x)
  have p0014 := @g_eleq2 (.cv b) C (.cv y)
  have p0015 :=
    @g_bibi12d (.classEq (.cv b) C) (.classMem (.cv x) (.cv b)) (.classMem (.cv x) C)
      (.classMem (.cv y) (.cv b)) (.classMem (.cv y) C) p0013 p0014
  have p0016 :=
    @g_notbid (.classEq (.cv b) C)
      (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))
      (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C)) p0015
  have p0017 :=
    @g_bibi12d (.classEq (.cv b) C) (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))
      (.classMem C (syn_csep2 (.cv x) (.cv y)))
      (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))))
      (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))) p0004 p0016
  have p0018 := @g_sep2valJp (.cv x) (.cv y) b dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0019 := @g_xor (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))
  have p0020 :=
    @g_bicomi (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b))))
        (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b)))))
      p0019
  have p0021 :=
    @g_bitri (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))
      (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b))))
        (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b)))))
      (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))) p0018 p0020
  have p0022 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))
        (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))))
      (syn_wb (.classMem C (syn_csep2 (.cv x) (.cv y)))
        (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))))
      b C (syn_cvv) dv_cache_0016 dv_cache_0021 p0017 p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
      (.classMem C (syn_cvv))
      (syn_wb (.classMem C (syn_csep2 (.cv x) (.cv y)))
        (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))))
      p0011 p0022
  have p0024 :=
    @g_notbid
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
      (.classMem C (syn_csep2 (.cv x) (.cv y)))
      (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))) p0023
  have p0025 :=
    @g_mpbid
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
      (.neg (.classMem C (syn_csep2 (.cv x) (.cv y))))
      (.neg (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C)))) p0008 p0024
  have p0026 :=
    @g_notnotrd
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A))
      (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C)) p0025
  exact p0026

@[expose]
noncomputable def g_fdrowrelex2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdrowrelex2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdrowrelex2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdrowrelex2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrowrel R A B) (syn_cvv))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have p0000 := (Nominal.classEqRefl (syn_cfdrowrel R A B))
  have p0001 :=
    @g_a1i
      (.classEq (syn_cfdrowrel R A B)
        (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))))
      (syn_wbr R (syn_cwe) A) p0000
  have p0002 := @g_fdmemex
  have p0003 := @g_kqrelex (syn_cfdmem) p0002
  have p0004 :=
    @g_a1i (.classMem (syn_ckqrel (syn_cfdmem)) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0003
  have p0005 :=
    @g_fdifex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdrowrelex2_1
      hyp_fdrowrelex2_2 hyp_fdrowrelex2_3
  have p0006 := @g_pw1exg (syn_cfdif R A B) (syn_cvv)
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdif R A B) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cfdif R A B)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_ckqrel (syn_cfdmem)) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cfdif R A B)) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_resexg (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B)) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_ckqrel (syn_cfdmem)) (syn_cvv))
        (.classMem (syn_cpw1 (syn_cfdif R A B)) (syn_cvv)))
      (.classMem (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))) (syn_cvv))
      p0008 p0009
  have p0011 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cfdrowrel R A B)
      (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))) (syn_cvv) p0001
      p0010
  exact p0011

@[expose]
noncomputable def g_elfdrowfibg (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (_dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (.classMem D (syn_cvv)) (syn_wb (.classMem D (syn_cfdrowfib R A B C))
          (.classMem (syn_cop (syn_csn D) C) (syn_cfdrowrel R A B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0011 : d ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_D, not_false_eq_true])
  have dv_cache_0012 :
    d ∉ ((Wff.classMem (syn_cop (syn_csn D) C) (syn_cfdrowrel R A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel, Finset.mem_union,
          fresh_d_not_D, fresh_d_not_C, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R,
          or_false, not_false_eq_true])
  have p0000 := @g_id (.classEq (.cv d) D)
  have p0001 := @g_sneqd (.classEq (.cv d) D) (.cv d) D p0000
  have p0002 := @g_opeq1d (.classEq (.cv d) D) (syn_csn (.cv d)) (syn_csn D) C p0001
  have p0003 :=
    @g_eleq1d (.classEq (.cv d) D) (syn_cop (syn_csn (.cv d)) C) (syn_cop (syn_csn D) C)
      (syn_cfdrowrel R A B) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrowfib A B C R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0005 :=
    @g_elab2g (.classMem (syn_cop (syn_csn (.cv d)) C) (syn_cfdrowrel R A B))
      (.classMem (syn_cop (syn_csn D) C) (syn_cfdrowrel R A B)) d D
      (syn_cfdrowfib R A B C) (syn_cvv) dv_cache_0011 dv_cache_0012 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_fdrowfibeq4 (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (.classEq C D) (.classEq (syn_cfdrowfib R A B C) (syn_cfdrowfib R A B D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : d ∉ ((Wff.classEq C D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_d_not_C, fresh_d_not_D, or_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (A).fv (B).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0003 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0007 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0009 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0010 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0011 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0012 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0013 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0014 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0015 : d ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_D, not_false_eq_true])
  have p0000 := @g_id (.classEq C D)
  have p0001 := @g_opeq2d (.classEq C D) C D (syn_csn (.cv d)) p0000
  have p0002 :=
    @g_eleq1d (.classEq C D) (syn_cop (syn_csn (.cv d)) C) (syn_cop (syn_csn (.cv d)) D)
      (syn_cfdrowrel R A B) p0001
  have p0003 :=
    @g_abbidv (.classEq C D)
      (.classMem (syn_cop (syn_csn (.cv d)) C) (syn_cfdrowrel R A B))
      (.classMem (syn_cop (syn_csn (.cv d)) D) (syn_cfdrowrel R A B)) d dv_cache_0001
      p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrowfib A B C R d
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrowfib A B D R d
      dv_cache_0002 dv_cache_0012 dv_cache_0004 dv_cache_0005 dv_cache_0013 dv_cache_0007
      dv_cache_0008 dv_cache_0014 dv_cache_0015 dv_cache_0011
  have p0006 :=
    @g_n_3eqtr4g (.classEq C D)
      (.cab d (.classMem (syn_cop (syn_csn (.cv d)) C) (syn_cfdrowrel R A B)))
      (.cab d (.classMem (syn_cop (syn_csn (.cv d)) D) (syn_cfdrowrel R A B)))
      (syn_cfdrowfib R A B C) (syn_cfdrowfib R A B D) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_fdrowfibsn2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdrowfibsn2_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfdrowfib R A B (syn_csn (syn_csn C))) (syn_cfdrow R A B C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((syn_csn (syn_csn C))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((syn_csn (syn_csn C))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint ((A).fv) (((syn_csn C)).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact (show Disjoint (A).fv (C).fv from (by exact dv_A_C))))))
  have dv_cache_0003 : Disjoint (A).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (A).fv from (by exact fresh_d_not_A))))))
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : Disjoint (B).fv ((syn_csn (syn_csn C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv ((syn_csn (syn_csn C))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint ((B).fv) (((syn_csn C)).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact (show Disjoint (B).fv (C).fv from (by exact dv_B_C))))))
  have dv_cache_0006 : Disjoint (B).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (B).fv from (by exact fresh_d_not_B))))))
  have dv_cache_0007 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : Disjoint ((syn_csn (syn_csn C))).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint ((syn_csn (syn_csn C))).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (((syn_csn C)).fv) (({ d } : Finset Var)) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact
                  (show Disjoint ((C).fv) (({ d } : Finset Var)) from
                    (Finset.disjoint_singleton_right.mpr
                      (show d ∉ (C).fv from (by exact fresh_d_not_C))))))))
  have dv_cache_0009 : Disjoint ((syn_csn (syn_csn C))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((syn_csn (syn_csn C))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint (((syn_csn C)).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact (show Disjoint (C).fv (R).fv from (by exact dv_C_R))))))
  have dv_cache_0010 : Disjoint ((Class.cv d)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint ((Class.cv d)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ d } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show d ∉ (R).fv from (by exact fresh_d_not_R))))))
  have dv_cache_0011 : Disjoint ((syn_cfdmem)).fv ((syn_csn (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint ((syn_cfdmem)).fv ((syn_csn (.cv d))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact (show Disjoint ((∅ : Finset Var)) (((Class.cv d)).fv) from (by simp))))
  have dv_cache_0012 : Disjoint ((syn_cfdmem)).fv ((syn_csn (syn_csn C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint ((syn_cfdmem)).fv ((syn_csn (syn_csn C))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact (show Disjoint ((∅ : Finset Var)) (((syn_csn C)).fv) from (by simp))))
  have dv_cache_0013 : Disjoint ((syn_csn (.cv d))).fv ((syn_csn (syn_csn C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint ((syn_csn (.cv d))).fv ((syn_csn (syn_csn C))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn ((Class.cv d)),
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn ((syn_csn C))];
          exact
            (show Disjoint (((Class.cv d)).fv) (((syn_csn C)).fv) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint (({ d } : Finset Var)) (((syn_csn C)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                      exact
                        (show Disjoint (({ d } : Finset Var)) ((C).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show d ∉ (C).fv from (by exact fresh_d_not_C))))))))))
  have dv_cache_0014 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0015 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0016 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0017 : Disjoint (C).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint (C).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (C).fv from (by exact fresh_d_not_C))))))
  have dv_cache_0018 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0019 : d ∉ ((syn_cfdrowfib R A B (syn_csn (syn_csn C)))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_d_not_A, fresh_d_not_B, fresh_d_not_C, fresh_d_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0020 : d ∉ ((syn_cfdrow R A B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_C, fresh_d_not_R,
          or_false, not_false_eq_true])
  have p0000 := @g_vex d
  have p0001 :=
    @g_elfdrowfibg A B (syn_csn (syn_csn C)) (.cv d) R dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_cfdrowrel R A B))
  have p0004 :=
    @g_eleq2i (syn_cfdrowrel R A B)
      (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B)))
      (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) p0003
  have p0005 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C))))
      (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdrowrel R A B))
      (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C)))
        (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))))
      p0002 p0004
  have p0006 :=
    @g_opelres (syn_csn (.cv d)) (syn_csn (syn_csn C)) (syn_ckqrel (syn_cfdmem))
      (syn_cpw1 (syn_cfdif R A B))
  have p0007 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C))))
      (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C)))
        (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C)))
          (syn_ckqrel (syn_cfdmem))) (.classMem (syn_csn (.cv d)) (syn_cpw1 (syn_cfdif R A B))))
      p0005 p0006
  have p0008 := @g_snex (.cv d)
  have p0009 := @g_snex (syn_csn C)
  have p0010 :=
    @g_kqrelbr (syn_cfdmem) (syn_csn (.cv d)) (syn_csn (syn_csn C)) dv_cache_0011
      dv_cache_0012 dv_cache_0013 p0008 p0009
  have p0011 := @g_snelpw1 (.cv d) (syn_cfdif R A B)
  have p0012 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_ckqrel (syn_cfdmem)))
      (.classMem (syn_copk (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem (syn_csn (.cv d)) (syn_cpw1 (syn_cfdif R A B)))
      (.classMem (.cv d) (syn_cfdif R A B)) p0010 p0011
  have p0013 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C)))
          (syn_ckqrel (syn_cfdmem))) (.classMem (syn_csn (.cv d)) (syn_cpw1 (syn_cfdif R A B))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdmem))
        (.classMem (.cv d) (syn_cfdif R A B)))
      p0007 p0012
  have p0014 := @g_fdmemval C d dv_cache_0014 hyp_fdrowfibsn2_1
  have p0015 :=
    @g_anbi1i (.classMem (syn_copk (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem C (.cv d)) (.classMem (.cv d) (syn_cfdif R A B)) p0014
  have p0016 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdmem))
        (.classMem (.cv d) (syn_cfdif R A B)))
      (syn_wa (.classMem C (.cv d)) (.classMem (.cv d) (syn_cfdif R A B))) p0013 p0015
  have p0017 := @g_ancom (.classMem C (.cv d)) (.classMem (.cv d) (syn_cfdif R A B))
  have p0018 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C))))
      (syn_wa (.classMem C (.cv d)) (.classMem (.cv d) (syn_cfdif R A B)))
      (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d))) p0016 p0017
  have p0019 :=
    @g_elfdrowg A B C (.cv d) R dv_cache_0001 dv_cache_0015 dv_cache_0003 dv_cache_0004
      dv_cache_0016 dv_cache_0006 dv_cache_0007 dv_cache_0017 dv_cache_0018 dv_cache_0010
  have p0020 :=
    @g_bicomi (.classMem (.cv d) (syn_cfdrow R A B C))
      (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d))) p0019
  have p0021 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C))))
      (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d)))
      (.classMem (.cv d) (syn_cfdrow R A B C)) p0018 p0020
  have p0022 :=
    @g_eqriv d (syn_cfdrowfib R A B (syn_csn (syn_csn C))) (syn_cfdrow R A B C)
      dv_cache_0019 dv_cache_0020 p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end
