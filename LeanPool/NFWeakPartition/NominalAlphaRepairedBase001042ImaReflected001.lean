/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001042ImaReflected001. -/


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
noncomputable def nominal_df_ima (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cima A B) (.cab x (syn_wrex y B (syn_wbr (.cv y) A (.cv x))))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alpha_dummy_002 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_003 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1)
  let alpha_dummy_004 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0)
  let alpha_dummy_005 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1)
  let alpha_dummy_006 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_002
              (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_002)
                  (syn_cphi (Class.cv alpha_dummy_003))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_002)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_003)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_007 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cphi (Class.cv alpha_dummy_005))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_008 : Var :=
    (freshVar (((Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cphi (Class.cv alpha_dummy_003)))))).fv ∪ ((Class.cab alpha_dummy_002
            (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cphi (Class.cv alpha_dummy_003)))))).fv) 0)
  let alpha_dummy_009 : Var :=
    (freshVar (((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv y)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cphi (Class.cv alpha_dummy_005)))))).fv ∪ ((Class.cab alpha_dummy_004
            (syn_wrex alpha_dummy_005 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cphi (Class.cv alpha_dummy_005)))))).fv) 0)
  let alpha_dummy_010 : Var := (freshVar (((Class.cv alpha_dummy_003)).fv) 0)
  let alpha_dummy_011 : Var := (freshVar (((Class.cv alpha_dummy_003)).fv) 1)
  let alpha_dummy_012 : Var := (freshVar (((Class.cv alpha_dummy_005)).fv) 0)
  let alpha_dummy_013 : Var := (freshVar (((Class.cv alpha_dummy_005)).fv) 1)
  let alpha_dummy_014 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_010) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_010) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_010)).fv) 0)
  let alpha_dummy_015 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_012) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_012) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_012)).fv) 0)
  let alpha_dummy_016 : Var :=
    (freshVar (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_017 : Var :=
    (freshVar (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_018 : Var :=
    (freshVar (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_019 : Var :=
    (freshVar (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_020 : Var :=
    (freshVar (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_021 : Var :=
    (freshVar (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_022 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018))).fv) 0)
  let alpha_dummy_023 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv) 0)
  let alpha_dummy_024 : Var :=
    (freshVar (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_018)).fv) 0)
  let alpha_dummy_025 : Var :=
    (freshVar (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_021)).fv) 0)
  let alpha_dummy_026 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_017))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_018))).fv) 0)
  let alpha_dummy_027 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_020))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_021))).fv) 0)
  let alpha_dummy_028 : Var :=
    (freshVar (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_017)).fv) 0)
  let alpha_dummy_029 : Var :=
    (freshVar (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_020)).fv) 0)
  let alpha_dummy_030 : Var :=
    (freshVar (((Class.cv alpha_dummy_018)).fv ∪ ((Class.cv alpha_dummy_018)).fv) 0)
  let alpha_dummy_031 : Var :=
    (freshVar (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_021)).fv) 0)
  let alpha_dummy_032 : Var :=
    (freshVar (((Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_003)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_003)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_033 : Var :=
    (freshVar (((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_034 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_003)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_035 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_005)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_036 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_003))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_003))).fv) 0)
  let alpha_dummy_037 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_005))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_005))).fv) 0)
  have fresh_046 : alpha_dummy_000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_047 : alpha_dummy_001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have support_mem_0000 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0001 :
    alpha_dummy_001 ∈
      (((syn_ccompl (Class.cab alpha_dummy_002
              (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_002)
                  (syn_cphi (Class.cv alpha_dummy_003))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_002)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_003))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0002 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0003 :
    y ∈
      (((syn_ccompl (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cphi (Class.cv alpha_dummy_005))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_005))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0004 :
    alpha_dummy_001 ∈
      (((Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cphi (Class.cv alpha_dummy_003)))))).fv ∪ ((Class.cab alpha_dummy_002
            (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cphi (Class.cv alpha_dummy_003)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0005 :
    y ∈
      (((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv y)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cphi (Class.cv alpha_dummy_005)))))).fv ∪ ((Class.cab alpha_dummy_004
            (syn_wrex alpha_dummy_005 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cphi (Class.cv alpha_dummy_005)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0006 : alpha_dummy_003 ∈ (((Class.cv alpha_dummy_003)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0007 : alpha_dummy_005 ∈ (((Class.cv alpha_dummy_005)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alpha_dummy_010 ∈
      (((Wff.classMem (Class.cv alpha_dummy_010) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_010) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_010)).fv) :=
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
  have support_mem_0009 :
    alpha_dummy_012 ∈
      (((Wff.classMem (Class.cv alpha_dummy_012) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_012) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_012)).fv) :=
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
  have support_mem_0010 :
    alpha_dummy_010 ∈ (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 :
    alpha_dummy_012 ∈ (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
    alpha_dummy_017 ∈
      (((syn_cnin (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 :
    alpha_dummy_020 ∈
      (((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 :
    alpha_dummy_017 ∈
      (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_018)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alpha_dummy_020 ∈
      (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_021)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alpha_dummy_018 ∈
      (((syn_cnin (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alpha_dummy_021 ∈
      (((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alpha_dummy_018 ∈
      (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_018)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alpha_dummy_021 ∈
      (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_021)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alpha_dummy_017 ∈
      (((syn_ccompl (Class.cv alpha_dummy_017))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_018))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alpha_dummy_020 ∈
      (((syn_ccompl (Class.cv alpha_dummy_020))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_021))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 :
    alpha_dummy_017 ∈
      (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_017)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    alpha_dummy_020 ∈
      (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_020)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0024 :
    alpha_dummy_018 ∈
      (((syn_ccompl (Class.cv alpha_dummy_017))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_018))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    alpha_dummy_021 ∈
      (((syn_ccompl (Class.cv alpha_dummy_020))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_021))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0026 :
    alpha_dummy_018 ∈
      (((Class.cv alpha_dummy_018)).fv ∪ ((Class.cv alpha_dummy_018)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0027 :
    alpha_dummy_021 ∈
      (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_021)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0028 :
    alpha_dummy_000 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0029 :
    alpha_dummy_000 ∈
      (((syn_ccompl (Class.cab alpha_dummy_002
              (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_002)
                  (syn_cphi (Class.cv alpha_dummy_003))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_002)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_003))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0030 : x ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0031 :
    x ∈
      (((syn_ccompl (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cphi (Class.cv alpha_dummy_005))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_005))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0032 :
    alpha_dummy_000 ∈
      (((Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_003)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_002 (syn_wrex alpha_dummy_003 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_003)) (syn_csn (syn_c0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0033 :
    x ∈
      (((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0034 :
    alpha_dummy_003 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_003)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0035 :
    alpha_dummy_005 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_005)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0036 :
    alpha_dummy_003 ∈
      (((syn_cphi (Class.cv alpha_dummy_003))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_003))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0037 :
    alpha_dummy_005 ∈
      (((syn_cphi (Class.cv alpha_dummy_005))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_005))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have focused_notmem_0000 : alpha_dummy_000 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (hu))
  have wpp_notmem_0000 : alpha_dummy_000 ∉ (B).fv := by exact focused_notmem_0000
  have wpp_notmem_0001 : x ∉ (B).fv := by exact dv_B_x
  have focused_notmem_0001 : alpha_dummy_001 ∉ B.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ B.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_right _ (hu))
  have wpp_notmem_0002 : alpha_dummy_001 ∉ (B).fv := by exact focused_notmem_0001
  have wpp_notmem_0003 : y ∉ (B).fv := by exact dv_B_y
  have wpp_refl_0000 : TReflOn [(alpha_dummy_001, y), (alpha_dummy_000, x)] (B).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))
  have wpp_notmem_0004 : alpha_dummy_000 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0005 : x ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0006 : alpha_dummy_001 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0007 : y ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0008 : alpha_dummy_006 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alpha_dummy_007 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alpha_dummy_008 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alpha_dummy_009 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alpha_dummy_002 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : alpha_dummy_004 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0014 : alpha_dummy_003 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0015 : alpha_dummy_005 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0016 : alpha_dummy_011 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alpha_dummy_013 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alpha_dummy_010 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alpha_dummy_012 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alpha_dummy_014 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alpha_dummy_015 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alpha_dummy_016 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : alpha_dummy_019 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alpha_dummy_017 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alpha_dummy_020 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0026 : alpha_dummy_018 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0027 : alpha_dummy_021 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
        (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
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
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have wpp_notmem_0028 : alpha_dummy_000 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0029 : x ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0030 : alpha_dummy_001 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0031 : y ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0032 : alpha_dummy_006 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0033 : alpha_dummy_007 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0034 : alpha_dummy_008 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0035 : alpha_dummy_009 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0036 : alpha_dummy_002 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0037 : alpha_dummy_004 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0038 : alpha_dummy_003 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0039 : alpha_dummy_005 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0040 : alpha_dummy_011 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0041 : alpha_dummy_013 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0042 : alpha_dummy_010 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0043 : alpha_dummy_012 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0044 : alpha_dummy_014 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alpha_dummy_015 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alpha_dummy_016 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alpha_dummy_019 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0048 : alpha_dummy_017 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0049 : alpha_dummy_020 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0050 : alpha_dummy_018 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0051 : alpha_dummy_021 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
        (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
      ((syn_c0)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
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
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
        (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_016)
            (syn_cun (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_019)
            (syn_cun (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
            (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
            (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
            (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
            (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_007),
            (alpha_dummy_001, y), (alpha_dummy_000, x)] (syn_c0) (by simp only [fv_syn_c0])))
      (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0052 : alpha_dummy_000 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0053 : x ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0054 : alpha_dummy_001 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0055 : y ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0056 : alpha_dummy_006 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0057 : alpha_dummy_007 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0058 : alpha_dummy_008 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0059 : alpha_dummy_009 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0060 : alpha_dummy_002 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0061 : alpha_dummy_004 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0062 : alpha_dummy_003 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0063 : alpha_dummy_005 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0064 : alpha_dummy_011 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0065 : alpha_dummy_013 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0066 : alpha_dummy_010 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0067 : alpha_dummy_012 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0068 : alpha_dummy_014 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0069 : alpha_dummy_015 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn
      [(alpha_dummy_014, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_012),
        (alpha_dummy_011, alpha_dummy_013), (alpha_dummy_003, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_004), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y), (alpha_dummy_000, x)]
      ((syn_cnnc)).fv :=
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
                        (TAlphaVar.free (by simp) (by simp)))))))))))
  have split_alpha_0001 :
    TAlphaWff
      [(alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_001)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_002) (syn_cphi (Class.cv alpha_dummy_003)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_005) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_004) (syn_cphi (Class.cv alpha_dummy_005))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective
                (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide))
              (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 1))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alpha_dummy_003)).fv) (by decide))
                      (freshVar_injective (((Class.cv alpha_dummy_005)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
        (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                      (TAlphaWff.neg split_alpha_0000))))))) (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_014, alpha_dummy_015),
                                (alpha_dummy_010, alpha_dummy_012),
                                (alpha_dummy_011, alpha_dummy_013),
                                (alpha_dummy_003, alpha_dummy_005),
                                (alpha_dummy_002, alpha_dummy_004),
                                (alpha_dummy_008, alpha_dummy_009),
                                (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y),
                                (alpha_dummy_000, x)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_014, alpha_dummy_015),
                                (alpha_dummy_010, alpha_dummy_012),
                                (alpha_dummy_011, alpha_dummy_013),
                                (alpha_dummy_003, alpha_dummy_005),
                                (alpha_dummy_002, alpha_dummy_004),
                                (alpha_dummy_008, alpha_dummy_009),
                                (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y),
                                (alpha_dummy_000, x)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0070 : alpha_dummy_032 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0071 : alpha_dummy_033 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0072 : alpha_dummy_034 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0073 : alpha_dummy_035 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0074 : alpha_dummy_036 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0075 : alpha_dummy_037 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0004 :
    TReflOn
      [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
        (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
        (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
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
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu))
                                  (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have wpp_notmem_0076 : alpha_dummy_032 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0077 : alpha_dummy_033 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0078 : alpha_dummy_034 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0079 : alpha_dummy_035 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0080 : alpha_dummy_036 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0081 : alpha_dummy_037 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0005 :
    TReflOn
      [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
        (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
        (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
      ((syn_c0)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0042) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0043) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0040) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0041) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                                  (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have split_alpha_0002 :
    TAlphaWff
      [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
        (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
        (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_016)
            (syn_cun (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_018)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_019)
            (syn_cun (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
            (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
            (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
            (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_034, alpha_dummy_035),
            (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
            (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_006, alpha_dummy_007),
            (alpha_dummy_001, y), (alpha_dummy_000, x)] (syn_c0) (by simp only [fv_syn_c0])))
      (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_010)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0082 : alpha_dummy_032 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0083 : alpha_dummy_033 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0084 : alpha_dummy_034 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alpha_dummy_035 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alpha_dummy_036 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alpha_dummy_037 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0006 :
    TReflOn
      [(alpha_dummy_014, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_012),
        (alpha_dummy_011, alpha_dummy_013), (alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_003, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_004), (alpha_dummy_032, alpha_dummy_033),
        (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y), (alpha_dummy_000, x)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0068) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0069) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0066) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0067) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0064) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0065) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0062) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0063) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0060) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0061) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                            (TAlphaVar.free (by simp) (by simp)))))))))))))
  have split_alpha_0003 :
    TAlphaWff
      [(alpha_dummy_036, alpha_dummy_037), (alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_036) (syn_cphi (Class.cv alpha_dummy_003)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_036)
            (syn_cphi (Class.cv alpha_dummy_003)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_037) (syn_cphi (Class.cv alpha_dummy_005)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_037)
            (syn_cphi (Class.cv alpha_dummy_005))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_003)).fv) (by decide))
                    (freshVar_injective (((Class.cv alpha_dummy_005)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_018, alpha_dummy_021),
        (alpha_dummy_017, alpha_dummy_020), (alpha_dummy_016, alpha_dummy_019),
        (alpha_dummy_014, alpha_dummy_015), (alpha_dummy_010, alpha_dummy_012),
        (alpha_dummy_011, alpha_dummy_013), (alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_003, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_004), (alpha_dummy_032, alpha_dummy_033),
        (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y), (alpha_dummy_000, x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg split_alpha_0002))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_014, alpha_dummy_015),
                              (alpha_dummy_010, alpha_dummy_012),
                              (alpha_dummy_011, alpha_dummy_013),
                              (alpha_dummy_036, alpha_dummy_037),
                              (alpha_dummy_034, alpha_dummy_035),
                              (alpha_dummy_003, alpha_dummy_005),
                              (alpha_dummy_002, alpha_dummy_004),
                              (alpha_dummy_032, alpha_dummy_033),
                              (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y),
                              (alpha_dummy_000, x)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_014, alpha_dummy_015),
                              (alpha_dummy_010, alpha_dummy_012),
                              (alpha_dummy_011, alpha_dummy_013),
                              (alpha_dummy_036, alpha_dummy_037),
                              (alpha_dummy_034, alpha_dummy_035),
                              (alpha_dummy_003, alpha_dummy_005),
                              (alpha_dummy_002, alpha_dummy_004),
                              (alpha_dummy_032, alpha_dummy_033),
                              (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y),
                              (alpha_dummy_000, x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 1)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alpha_dummy_003)).fv) (by decide))
                      (freshVar_injective (((Class.cv alpha_dummy_005)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [(alpha_dummy_018, alpha_dummy_021), (alpha_dummy_017, alpha_dummy_020),
        (alpha_dummy_016, alpha_dummy_019), (alpha_dummy_014, alpha_dummy_015),
        (alpha_dummy_010, alpha_dummy_012), (alpha_dummy_011, alpha_dummy_013),
        (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                      (TAlphaWff.neg split_alpha_0002))))))) (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_014, alpha_dummy_015),
                                (alpha_dummy_010, alpha_dummy_012),
                                (alpha_dummy_011, alpha_dummy_013),
                                (alpha_dummy_036, alpha_dummy_037),
                                (alpha_dummy_034, alpha_dummy_035),
                                (alpha_dummy_003, alpha_dummy_005),
                                (alpha_dummy_002, alpha_dummy_004),
                                (alpha_dummy_032, alpha_dummy_033),
                                (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y),
                                (alpha_dummy_000, x)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_014, alpha_dummy_015),
                                (alpha_dummy_010, alpha_dummy_012),
                                (alpha_dummy_011, alpha_dummy_013),
                                (alpha_dummy_036, alpha_dummy_037),
                                (alpha_dummy_034, alpha_dummy_035),
                                (alpha_dummy_003, alpha_dummy_005),
                                (alpha_dummy_002, alpha_dummy_004),
                                (alpha_dummy_032, alpha_dummy_033),
                                (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y),
                                (alpha_dummy_000, x)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0088 : alpha_dummy_000 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0089 : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0090 : alpha_dummy_001 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0091 : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0092 : alpha_dummy_006 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0093 : alpha_dummy_007 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0094 : alpha_dummy_032 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0095 : alpha_dummy_033 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0096 : alpha_dummy_002 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0097 : alpha_dummy_004 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0098 : alpha_dummy_003 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0099 : alpha_dummy_005 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0100 : alpha_dummy_034 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0101 : alpha_dummy_035 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_refl_0007 :
    TReflOn
      [(alpha_dummy_034, alpha_dummy_035), (alpha_dummy_003, alpha_dummy_005),
        (alpha_dummy_002, alpha_dummy_004), (alpha_dummy_032, alpha_dummy_033),
        (alpha_dummy_006, alpha_dummy_007), (alpha_dummy_001, y), (alpha_dummy_000, x)]
      ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0100) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0101) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0098) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0099) (h_eq ▸ hu))
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
                    (TAlphaVar.free (by simp) (by simp)))))))))
  have focused_notmem_0002 : alpha_dummy_000 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have wpp_notmem_0102 : alpha_dummy_000 ∉ (A).fv := by exact focused_notmem_0002
  have wpp_notmem_0103 : x ∉ (A).fv := by exact dv_A_x
  have focused_notmem_0003 : alpha_dummy_001 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ (B).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have wpp_notmem_0104 : alpha_dummy_001 ∉ (A).fv := by exact focused_notmem_0003
  have wpp_notmem_0105 : y ∉ (A).fv := by exact dv_A_y
  have wpp_refl_0008 : TReflOn [(alpha_dummy_001, y), (alpha_dummy_000, x)] (A).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0104) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0105) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0102) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0103) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp))))
  have split_alpha_0004 :
    TAlphaWff [(alpha_dummy_001, y), (alpha_dummy_000, x)]
      (Wff.classMem (syn_cop (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)) A)
      (Wff.classMem (syn_cop (Class.cv y) (Class.cv x)) A) :=
    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg split_alpha_0001))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg split_alpha_0001))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0029 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪
                                      ((Class.cv alpha_dummy_000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)] (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0029 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪
                                      ((Class.cv alpha_dummy_000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004),
        (alpha_dummy_032, alpha_dummy_033), (alpha_dummy_006, alpha_dummy_007),
        (alpha_dummy_001, y), (alpha_dummy_000, x)] (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))
      (TAlphaClass.refl_of_reflOn [(alpha_dummy_001, y), (alpha_dummy_000, x)] A wpp_refl_0008))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_reflOn [(alpha_dummy_001, y), (alpha_dummy_000, x)] B
                wpp_refl_0000)) split_alpha_0004)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
