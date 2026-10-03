/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001034OpReflected001. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

@[expose]
noncomputable def nominal_df_op (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cop A B)
        (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x
            (syn_wrex y B
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alpha_dummy_002 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
                (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cphi (Class.cv alpha_dummy_001))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_003 : Var :=
    (freshVar (((syn_ccompl (Class.cab x
              (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y))))))).fv ∪
        ((syn_ccompl (Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                  (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c)))))))).fv) 0)
  let alpha_dummy_004 : Var :=
    (freshVar (((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
              (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cphi (Class.cv alpha_dummy_001)))))).fv ∪ ((Class.cab alpha_dummy_000
            (syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cphi (Class.cv alpha_dummy_001)))))).fv) 0)
  let alpha_dummy_005 : Var :=
    (freshVar (((Class.cab x
            (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).fv ∪
        ((Class.cab x (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_007 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 1)
  let alpha_dummy_008 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alpha_dummy_009 : Var := (freshVar (((Class.cv y)).fv) 1)
  let alpha_dummy_010 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_006) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_006) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_006)).fv) 0)
  let alpha_dummy_011 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_008) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_008) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_008)).fv) 0)
  let alpha_dummy_012 : Var :=
    (freshVar (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_013 : Var :=
    (freshVar (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_014 : Var :=
    (freshVar (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_015 : Var :=
    (freshVar (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_016 : Var :=
    (freshVar (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_017 : Var :=
    (freshVar (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_018 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014))).fv) 0)
  let alpha_dummy_019 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) 0)
  let alpha_dummy_020 : Var :=
    (freshVar (((Class.cv alpha_dummy_013)).fv ∪ ((Class.cv alpha_dummy_014)).fv) 0)
  let alpha_dummy_021 : Var :=
    (freshVar (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_017)).fv) 0)
  let alpha_dummy_022 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_013))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_014))).fv) 0)
  let alpha_dummy_023 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_016))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_017))).fv) 0)
  let alpha_dummy_024 : Var :=
    (freshVar (((Class.cv alpha_dummy_013)).fv ∪ ((Class.cv alpha_dummy_013)).fv) 0)
  let alpha_dummy_025 : Var :=
    (freshVar (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_016)).fv) 0)
  let alpha_dummy_026 : Var :=
    (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((Class.cv alpha_dummy_014)).fv) 0)
  let alpha_dummy_027 : Var :=
    (freshVar (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_017)).fv) 0)
  let alpha_dummy_028 : Var :=
    (freshVar (((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
              (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
              (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_029 : Var :=
    (freshVar (((Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab x
            (syn_wrex y B (Wff.classEq (Class.cv x)
                (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_030 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_031 : Var :=
    (freshVar
      (((syn_ccompl (syn_cphi (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_032 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_001))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_001))).fv) 0)
  let alpha_dummy_033 : Var :=
    (freshVar (((syn_cphi (Class.cv y))).fv ∪ ((syn_cphi (Class.cv y))).fv) 0)
  have fresh_000 :
    alpha_dummy_004 ∉
      (((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
              (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cphi (Class.cv alpha_dummy_001)))))).fv ∪ ((Class.cab alpha_dummy_000
            (syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cphi (Class.cv alpha_dummy_001)))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
                (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cphi (Class.cv alpha_dummy_001)))))).fv ∪ ((Class.cab alpha_dummy_000
              (syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cphi (Class.cv alpha_dummy_001)))))).fv)
        0
  have fresh_001 :
    alpha_dummy_028 ∉
      (((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
              (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
              (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c))))))).fv ∪
          ((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c))))))).fv)
        0
  have fresh_002 :
    alpha_dummy_005 ∉
      (((Class.cab x (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).fv ∪
        ((Class.cab x (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab x (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).fv ∪
          ((Class.cab x (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).fv)
        0
  have fresh_003 :
    alpha_dummy_029 ∉
      (((Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab x
            (syn_wrex y B (Wff.classEq (Class.cv x)
                (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                  (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab x
              (syn_wrex y B (Wff.classEq (Class.cv x)
                  (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).fv)
        0
  have fresh_030 :
    alpha_dummy_002 ∉
      (((syn_ccompl (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
                (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cphi (Class.cv alpha_dummy_001))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_001))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_ccompl (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
                  (Wff.classEq (Class.cv alpha_dummy_000)
                    (syn_cphi (Class.cv alpha_dummy_001))))))).fv ∪ ((syn_ccompl
              (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                  (Wff.classEq (Class.cv alpha_dummy_000)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c)))))))).fv)
        0
  have fresh_031 :
    alpha_dummy_003 ∉
      (((syn_ccompl (Class.cab x
              (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y))))))).fv ∪
        ((syn_ccompl (Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                  (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c)))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_ccompl (Class.cab x
                (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y))))))).fv ∪
          ((syn_ccompl (Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                    (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c)))))))).fv)
        0
  have fresh_040 : alpha_dummy_000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_041 : alpha_dummy_001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have support_mem_0000 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0001 : y ∈ (((Class.cv y)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0002 :
    alpha_dummy_006 ∈
      (((Wff.classMem (Class.cv alpha_dummy_006) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_006) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_006)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_wff_classMem]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0003 :
    alpha_dummy_008 ∈
      (((Wff.classMem (Class.cv alpha_dummy_008) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_008) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_008)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_wff_classMem]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0004 :
    alpha_dummy_006 ∈ (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 :
    alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0006 :
    alpha_dummy_013 ∈
      (((syn_cnin (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0007 :
    alpha_dummy_016 ∈
      (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alpha_dummy_013 ∈
      (((Class.cv alpha_dummy_013)).fv ∪ ((Class.cv alpha_dummy_014)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0009 :
    alpha_dummy_016 ∈
      (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_017)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0010 :
    alpha_dummy_014 ∈
      (((syn_cnin (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 :
    alpha_dummy_017 ∈
      (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
    alpha_dummy_014 ∈
      (((Class.cv alpha_dummy_013)).fv ∪ ((Class.cv alpha_dummy_014)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 :
    alpha_dummy_017 ∈
      (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_017)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 :
    alpha_dummy_013 ∈
      (((syn_ccompl (Class.cv alpha_dummy_013))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_014))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alpha_dummy_016 ∈
      (((syn_ccompl (Class.cv alpha_dummy_016))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_017))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alpha_dummy_013 ∈
      (((Class.cv alpha_dummy_013)).fv ∪ ((Class.cv alpha_dummy_013)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alpha_dummy_016 ∈
      (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_016)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alpha_dummy_014 ∈
      (((syn_ccompl (Class.cv alpha_dummy_013))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_014))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alpha_dummy_017 ∈
      (((syn_ccompl (Class.cv alpha_dummy_016))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_017))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alpha_dummy_014 ∈
      (((Class.cv alpha_dummy_014)).fv ∪ ((Class.cv alpha_dummy_014)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alpha_dummy_017 ∈
      (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_017)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 :
    alpha_dummy_001 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    y ∈
      (((syn_ccompl (syn_cphi (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0024 :
    alpha_dummy_001 ∈
      (((syn_cphi (Class.cv alpha_dummy_001))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_001))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    y ∈ (((syn_cphi (Class.cv y))).fv ∪ ((syn_cphi (Class.cv y))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have focused_notmem_0000 : alpha_dummy_001 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0001 : alpha_dummy_000 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0002 : alpha_dummy_002 ∉ A.fv :=
    by
    change
      freshVar
          (((syn_ccompl (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
                    (Wff.classEq (Class.cv alpha_dummy_000)
                      (syn_cphi (Class.cv alpha_dummy_001))))))).fv ∪ ((syn_ccompl
                (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                    (Wff.classEq (Class.cv alpha_dummy_000)
                      (syn_cun (syn_cphi (Class.cv alpha_dummy_001))
                        (syn_csn (syn_c0c)))))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_syn_ccompl (Class.cab alpha_dummy_000
                    (syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                        (syn_cphi (Class.cv alpha_dummy_001)))))).symm ▸
              (((fv_class_cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
                      (Wff.classEq (Class.cv alpha_dummy_000)
                        (syn_cphi (Class.cv alpha_dummy_001))))).symm ▸ (Finset.mem_erase.mpr
                  ⟨(fun h_eq => (focused_notmem_0001) (h_eq ▸ hu)),
                    (((fv_syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                            (syn_cphi (Class.cv alpha_dummy_001)))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (focused_notmem_0000) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0000 : alpha_dummy_002 ∉ (A).fv := by exact focused_notmem_0002
  have focused_notmem_0003 : alpha_dummy_003 ∉ A.fv :=
    by
    change
      freshVar
          (((syn_ccompl (Class.cab x (syn_wrex y A
                    (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y))))))).fv ∪ ((syn_ccompl
                (Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                      (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c)))))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_syn_ccompl (Class.cab x (syn_wrex y A
                      (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).symm ▸
              (((fv_class_cab x (syn_wrex y A
                      (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y))))).symm ▸
                (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)), (((fv_syn_wrex y A
                          (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (dv_A_y) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0001 : alpha_dummy_003 ∉ (A).fv := by exact focused_notmem_0003
  have focused_notmem_0004 : alpha_dummy_004 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
                  (Wff.classEq (Class.cv alpha_dummy_000)
                    (syn_cphi (Class.cv alpha_dummy_001)))))).fv ∪ ((Class.cab alpha_dummy_000
                (syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                    (syn_cphi (Class.cv alpha_dummy_001)))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab alpha_dummy_000
                  (syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                      (syn_cphi (Class.cv alpha_dummy_001))))).symm ▸ (Finset.mem_erase.mpr
                ⟨(fun h_eq => (focused_notmem_0001) (h_eq ▸ hu)),
                  (((fv_syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                          (syn_cphi (Class.cv alpha_dummy_001)))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0000) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0002 : alpha_dummy_004 ∉ (A).fv := by exact focused_notmem_0004
  have focused_notmem_0005 : alpha_dummy_005 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab x
                (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).fv ∪
            ((Class.cab x
                (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab x (syn_wrex y A
                    (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y))))).symm ▸
              (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)), (((fv_syn_wrex y A
                        (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_A_y) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0003 : alpha_dummy_005 ∉ (A).fv := by exact focused_notmem_0005
  have wpp_notmem_0004 : alpha_dummy_000 ∉ (A).fv := by exact focused_notmem_0001
  have wpp_notmem_0005 : x ∉ (A).fv := by exact dv_A_x
  have wpp_notmem_0006 : alpha_dummy_001 ∉ (A).fv := by exact focused_notmem_0000
  have wpp_notmem_0007 : y ∉ (A).fv := by exact dv_A_y
  have wpp_refl_0000 :
    TReflOn
      [(alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_004, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_003)]
      (A).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu))
              (TAlphaVar.free (by simp) (by simp))))))
  have wpp_notmem_0008 : alpha_dummy_002 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alpha_dummy_003 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alpha_dummy_004 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alpha_dummy_005 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alpha_dummy_000 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : x ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0014 : alpha_dummy_001 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0015 : y ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0016 : alpha_dummy_007 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alpha_dummy_009 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alpha_dummy_006 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alpha_dummy_008 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alpha_dummy_010 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alpha_dummy_011 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alpha_dummy_012 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : alpha_dummy_015 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alpha_dummy_013 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alpha_dummy_016 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0026 : alpha_dummy_014 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0027 : alpha_dummy_017 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
        (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_004, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c1c)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0014) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0015) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0012) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0013) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0010) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0011) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0008) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0009) (h_eq ▸ hu))
                          (TAlphaVar.free (by simp) (by simp))))))))))))
  have wpp_notmem_0028 : alpha_dummy_002 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0029 : alpha_dummy_003 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0030 : alpha_dummy_004 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0031 : alpha_dummy_005 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0032 : alpha_dummy_000 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0033 : x ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0034 : alpha_dummy_001 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0035 : y ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0036 : alpha_dummy_007 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0037 : alpha_dummy_009 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0038 : alpha_dummy_006 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0039 : alpha_dummy_008 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0040 : alpha_dummy_010 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0041 : alpha_dummy_011 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0042 : alpha_dummy_012 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0043 : alpha_dummy_015 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0044 : alpha_dummy_013 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alpha_dummy_016 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alpha_dummy_014 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alpha_dummy_017 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
        (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_004, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c0)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0042) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0043) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0040) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0041) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0034) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0035) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                          (TAlphaVar.free (by simp) (by simp))))))))))))
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
        (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_004, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_012)
            (syn_cun (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_015)
            (syn_cun (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
            (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
            (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
            (alpha_dummy_001, y), (alpha_dummy_000, x),
            (alpha_dummy_004, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_003)]
          (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0048 : alpha_dummy_002 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0049 : alpha_dummy_003 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0050 : alpha_dummy_004 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0051 : alpha_dummy_005 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0052 : alpha_dummy_000 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0053 : x ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0054 : alpha_dummy_001 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0055 : y ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0056 : alpha_dummy_007 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0057 : alpha_dummy_009 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0058 : alpha_dummy_006 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0059 : alpha_dummy_008 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0060 : alpha_dummy_010 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0061 : alpha_dummy_011 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn
      [(alpha_dummy_010, alpha_dummy_011), (alpha_dummy_006, alpha_dummy_008),
        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_004, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0060) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0061) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
                    (TAlphaVar.free (by simp) (by simp)))))))))
  have split_alpha_0001 :
    TAlphaWff [(alpha_dummy_004, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_004) (Class.cab alpha_dummy_000
            (syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                (syn_cphi (Class.cv alpha_dummy_001)))))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_004) (Class.cab alpha_dummy_000
              (syn_wrex alpha_dummy_001 A (Wff.classEq (Class.cv alpha_dummy_000)
                  (syn_cphi (Class.cv alpha_dummy_001))))))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_005)
          (Class.cab x (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y))))))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_005) (Class.cab x
              (syn_wrex y A (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y)))))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_reflOn [(alpha_dummy_001, y), (alpha_dummy_000, x),
                    (alpha_dummy_004, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_003)]
                  A wpp_refl_0000)) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv)
                              (by decide)) (freshVar_injective (((Class.cv y)).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [(alpha_dummy_014, alpha_dummy_017),
        (alpha_dummy_013, alpha_dummy_016), (alpha_dummy_012, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_006, alpha_dummy_008),
        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_004, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_003)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg split_alpha_0000)))))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [(alpha_dummy_010, alpha_dummy_011),
                                      (alpha_dummy_006, alpha_dummy_008),
                                      (alpha_dummy_007, alpha_dummy_009),
                                      (alpha_dummy_001, y), (alpha_dummy_000, x),
                                      (alpha_dummy_004, alpha_dummy_005),
                                      (alpha_dummy_002, alpha_dummy_003)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [(alpha_dummy_010, alpha_dummy_011),
                                      (alpha_dummy_006, alpha_dummy_008),
                                      (alpha_dummy_007, alpha_dummy_009),
                                      (alpha_dummy_001, y), (alpha_dummy_000, x),
                                      (alpha_dummy_004, alpha_dummy_005),
                                      (alpha_dummy_002, alpha_dummy_003)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_reflOn [(alpha_dummy_001, y), (alpha_dummy_000, x),
                      (alpha_dummy_004, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_003)]
                    A wpp_refl_0000)) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                      dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                                (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                            (TAlphaVar.there
                              (freshVar_injective (((Class.cv alpha_dummy_001)).fv) (by decide))
                              (freshVar_injective (((Class.cv y)).fv) (by decide))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003
        0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
        (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_004, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_003)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.neg split_alpha_0000))))))) (TAlphaWff.classMem (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.refl_of_closed
                                      [(alpha_dummy_010, alpha_dummy_011),
                                        (alpha_dummy_006, alpha_dummy_008),
                                        (alpha_dummy_007, alpha_dummy_009),
                                        (alpha_dummy_001, y), (alpha_dummy_000, x),
                                        (alpha_dummy_004, alpha_dummy_005),
                                        (alpha_dummy_002, alpha_dummy_003)]
                                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                              (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                      [(alpha_dummy_010, alpha_dummy_011),
                                        (alpha_dummy_006, alpha_dummy_008),
                                        (alpha_dummy_007, alpha_dummy_009),
                                        (alpha_dummy_001, y), (alpha_dummy_000, x),
                                        (alpha_dummy_004, alpha_dummy_005),
                                        (alpha_dummy_002, alpha_dummy_003)] (syn_cnnc)
                                      (by simp only [fv_syn_cnnc]))))))))))))))))))
  have focused_notmem_0006 : alpha_dummy_001 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_right _ (hu))
  have focused_notmem_0007 : alpha_dummy_000 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (hu))
  have focused_notmem_0008 : alpha_dummy_002 ∉ B.fv :=
    by
    change
      freshVar
          (((syn_ccompl (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 A
                    (Wff.classEq (Class.cv alpha_dummy_000)
                      (syn_cphi (Class.cv alpha_dummy_001))))))).fv ∪ ((syn_ccompl
                (Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                    (Wff.classEq (Class.cv alpha_dummy_000)
                      (syn_cun (syn_cphi (Class.cv alpha_dummy_001))
                        (syn_csn (syn_c0c)))))))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_ccompl (Class.cab alpha_dummy_000
                    (syn_wrex alpha_dummy_001 B (Wff.classEq (Class.cv alpha_dummy_000)
                        (syn_cun (syn_cphi (Class.cv alpha_dummy_001))
                          (syn_csn (syn_c0c))))))).symm ▸ (((fv_class_cab alpha_dummy_000
                    (syn_wrex alpha_dummy_001 B (Wff.classEq (Class.cv alpha_dummy_000)
                        (syn_cun (syn_cphi (Class.cv alpha_dummy_001))
                          (syn_csn (syn_c0c)))))).symm ▸ (Finset.mem_erase.mpr
                  ⟨(fun h_eq => (focused_notmem_0007) (h_eq ▸ hu)),
                    (((fv_syn_wrex alpha_dummy_001 B (Wff.classEq (Class.cv alpha_dummy_000)
                            (syn_cun (syn_cphi (Class.cv alpha_dummy_001))
                              (syn_csn (syn_c0c))))).symm ▸ (Finset.mem_union_left _
                        (Finset.mem_erase.mpr ⟨(fun h_eq => (focused_notmem_0006) (h_eq ▸ hu)),
                            (hu)⟩))))⟩))))))
  have wpp_notmem_0062 : alpha_dummy_002 ∉ (B).fv := by exact focused_notmem_0008
  have focused_notmem_0009 : alpha_dummy_003 ∉ B.fv :=
    by
    change
      freshVar
          (((syn_ccompl (Class.cab x (syn_wrex y A
                    (Wff.classEq (Class.cv x) (syn_cphi (Class.cv y))))))).fv ∪ ((syn_ccompl
                (Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                      (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c)))))))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_ccompl (Class.cab x (syn_wrex y B
                      (Wff.classEq (Class.cv x)
                        (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).symm ▸
              (((fv_class_cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                        (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c)))))).symm ▸
                (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_B_x) (h_eq ▸ hu)), (((fv_syn_wrex y B
                          (Wff.classEq (Class.cv x)
                            (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (dv_B_y) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0063 : alpha_dummy_003 ∉ (B).fv := by exact focused_notmem_0009
  have focused_notmem_0010 : alpha_dummy_028 ∉ B.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                  (Wff.classEq (Class.cv alpha_dummy_000)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c))))))).fv ∪
            ((Class.cab alpha_dummy_000 (syn_wrex alpha_dummy_001 B
                  (Wff.classEq (Class.cv alpha_dummy_000)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_001)) (syn_csn (syn_c0c))))))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab alpha_dummy_000
                  (syn_wrex alpha_dummy_001 B (Wff.classEq (Class.cv alpha_dummy_000)
                      (syn_cun (syn_cphi (Class.cv alpha_dummy_001))
                        (syn_csn (syn_c0c)))))).symm ▸ (Finset.mem_erase.mpr
                ⟨(fun h_eq => (focused_notmem_0007) (h_eq ▸ hu)),
                  (((fv_syn_wrex alpha_dummy_001 B (Wff.classEq (Class.cv alpha_dummy_000)
                          (syn_cun (syn_cphi (Class.cv alpha_dummy_001))
                            (syn_csn (syn_c0c))))).symm ▸ (Finset.mem_union_left _
                      (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0006) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0064 : alpha_dummy_028 ∉ (B).fv := by exact focused_notmem_0010
  have focused_notmem_0011 : alpha_dummy_029 ∉ B.fv :=
    by
    change
      freshVar
          (((Class.cab x (syn_wrex y B (Wff.classEq (Class.cv x)
                    (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab x
                (syn_wrex y B (Wff.classEq (Class.cv x)
                    (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))))).fv)
          0 ∉
        B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab x (syn_wrex y B
                    (Wff.classEq (Class.cv x)
                      (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c)))))).symm ▸
              (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_B_x) (h_eq ▸ hu)), (((fv_syn_wrex y B
                        (Wff.classEq (Class.cv x)
                          (syn_cun (syn_cphi (Class.cv y)) (syn_csn (syn_c0c))))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_B_y) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0065 : alpha_dummy_029 ∉ (B).fv := by exact focused_notmem_0011
  have wpp_notmem_0066 : alpha_dummy_000 ∉ (B).fv := by exact focused_notmem_0007
  have wpp_notmem_0067 : x ∉ (B).fv := by exact dv_B_x
  have wpp_notmem_0068 : alpha_dummy_001 ∉ (B).fv := by exact focused_notmem_0006
  have wpp_notmem_0069 : y ∉ (B).fv := by exact dv_B_y
  have wpp_refl_0004 :
    TReflOn
      [(alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
        (alpha_dummy_002, alpha_dummy_003)]
      (B).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0068) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0069) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0066) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0067) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0064) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0065) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0062) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0063) (h_eq ▸ hu))
              (TAlphaVar.free (by simp) (by simp))))))
  have wpp_notmem_0070 : alpha_dummy_028 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0071 : alpha_dummy_029 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0072 : alpha_dummy_030 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0073 : alpha_dummy_031 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0074 : alpha_dummy_032 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0075 : alpha_dummy_033 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0005 :
    TReflOn
      [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
        (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_030, alpha_dummy_031),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c1c)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0014) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0015) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0012) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0013) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0070) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0071) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0008) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0009) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have wpp_notmem_0076 : alpha_dummy_028 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0077 : alpha_dummy_029 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0078 : alpha_dummy_030 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0079 : alpha_dummy_031 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0080 : alpha_dummy_032 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0081 : alpha_dummy_033 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0006 :
    TReflOn
      [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
        (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_030, alpha_dummy_031),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c0)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0042) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0043) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0040) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0041) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0034) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0035) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have split_alpha_0002 :
    TAlphaWff
      [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
        (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_030, alpha_dummy_031),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
        (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_012)
            (syn_cun (Class.cv alpha_dummy_013) (Class.cv alpha_dummy_014)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_015)
            (syn_cun (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
            (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
            (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
            (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_030, alpha_dummy_031),
            (alpha_dummy_001, y), (alpha_dummy_000, x),
            (alpha_dummy_028, alpha_dummy_029), (alpha_dummy_002, alpha_dummy_003)]
          (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_006)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0082 : alpha_dummy_028 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0083 : alpha_dummy_029 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0084 : alpha_dummy_030 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alpha_dummy_031 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alpha_dummy_032 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alpha_dummy_033 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0007 :
    TReflOn
      [(alpha_dummy_010, alpha_dummy_011), (alpha_dummy_006, alpha_dummy_008),
        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_032, alpha_dummy_033),
        (alpha_dummy_030, alpha_dummy_031), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_028, alpha_dummy_029), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0060) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0061) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
                        (TAlphaVar.free (by simp) (by simp)))))))))))
  have split_alpha_0003 :
    TAlphaWff
      [(alpha_dummy_032, alpha_dummy_033), (alpha_dummy_030, alpha_dummy_031),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
        (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_032) (syn_cphi (Class.cv alpha_dummy_001)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_032)
            (syn_cphi (Class.cv alpha_dummy_001)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_033) (syn_cphi (Class.cv y)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_033) (syn_cphi (Class.cv y))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_001)).fv) (by decide))
                    (freshVar_injective (((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_014, alpha_dummy_017),
        (alpha_dummy_013, alpha_dummy_016), (alpha_dummy_012, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_006, alpha_dummy_008),
        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_032, alpha_dummy_033),
        (alpha_dummy_030, alpha_dummy_031), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_028, alpha_dummy_029), (alpha_dummy_002, alpha_dummy_003)]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg split_alpha_0002))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_010, alpha_dummy_011),
                              (alpha_dummy_006, alpha_dummy_008),
                              (alpha_dummy_007, alpha_dummy_009),
                              (alpha_dummy_032, alpha_dummy_033),
                              (alpha_dummy_030, alpha_dummy_031), (alpha_dummy_001, y),
                              (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
                              (alpha_dummy_002, alpha_dummy_003)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_010, alpha_dummy_011),
                              (alpha_dummy_006, alpha_dummy_008),
                              (alpha_dummy_007, alpha_dummy_009),
                              (alpha_dummy_032, alpha_dummy_033),
                              (alpha_dummy_030, alpha_dummy_031), (alpha_dummy_001, y),
                              (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
                              (alpha_dummy_002, alpha_dummy_003)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alpha_dummy_001)).fv) (by decide))
                      (freshVar_injective (((Class.cv y)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [(alpha_dummy_014, alpha_dummy_017), (alpha_dummy_013, alpha_dummy_016),
        (alpha_dummy_012, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_006, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_030, alpha_dummy_031),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
        (alpha_dummy_002, alpha_dummy_003)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                      (TAlphaWff.neg split_alpha_0002))))))) (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_010, alpha_dummy_011),
                                (alpha_dummy_006, alpha_dummy_008),
                                (alpha_dummy_007, alpha_dummy_009),
                                (alpha_dummy_032, alpha_dummy_033),
                                (alpha_dummy_030, alpha_dummy_031), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
                                (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_010, alpha_dummy_011),
                                (alpha_dummy_006, alpha_dummy_008),
                                (alpha_dummy_007, alpha_dummy_009),
                                (alpha_dummy_032, alpha_dummy_033),
                                (alpha_dummy_030, alpha_dummy_031), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
                                (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0088 : alpha_dummy_002 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0089 : alpha_dummy_003 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0090 : alpha_dummy_028 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0091 : alpha_dummy_029 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0092 : alpha_dummy_000 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0093 : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0094 : alpha_dummy_001 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0095 : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0096 : alpha_dummy_030 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0097 : alpha_dummy_031 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_refl_0008 :
    TReflOn
      [(alpha_dummy_030, alpha_dummy_031), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_028, alpha_dummy_029), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0096) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0097) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0094) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0095) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu))
                (TAlphaVar.free (by simp) (by simp)))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0001))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_reflOn
                                [(alpha_dummy_001, y), (alpha_dummy_000, x),
                                  (alpha_dummy_028, alpha_dummy_029),
                                  (alpha_dummy_002, alpha_dummy_003)] B wpp_refl_0004))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_030, alpha_dummy_031),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
        (alpha_dummy_002, alpha_dummy_003)] (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_reflOn
                                [(alpha_dummy_001, y), (alpha_dummy_000, x),
                                  (alpha_dummy_028, alpha_dummy_029),
                                  (alpha_dummy_002, alpha_dummy_003)] B wpp_refl_0004))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_030, alpha_dummy_031),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_028, alpha_dummy_029),
        (alpha_dummy_002, alpha_dummy_003)] (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
