/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001046CnvReflected001. -/


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
noncomputable def nominal_df_cnv (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_ccnv A) (syn_copab x y (syn_wbr (.cv y) A (.cv x)))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv) 1)
  let alpha_dummy_002 : Var :=
    (freshVar (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
        ((syn_wbr (Class.cv alpha_dummy_001) A (Class.cv alpha_dummy_000))).fv) 0)
  let alpha_dummy_003 : Var :=
    (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wbr (Class.cv y) A (Class.cv x))).fv) 0)
  let alpha_dummy_004 : Var :=
    (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_005 : Var :=
    (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 1)
  let alpha_dummy_006 : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)
  let alpha_dummy_007 : Var := (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)
  let alpha_dummy_008 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_004
              (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cphi (Class.cv alpha_dummy_005))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_009 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_010 : Var :=
    (freshVar (((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cphi (Class.cv alpha_dummy_005)))))).fv ∪ ((Class.cab alpha_dummy_004
            (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cphi (Class.cv alpha_dummy_005)))))).fv) 0)
  let alpha_dummy_011 : Var :=
    (freshVar (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cphi (Class.cv alpha_dummy_007)))))).fv ∪ ((Class.cab alpha_dummy_006
            (syn_wrex alpha_dummy_007 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cphi (Class.cv alpha_dummy_007)))))).fv) 0)
  let alpha_dummy_012 : Var := (freshVar (((Class.cv alpha_dummy_005)).fv) 0)
  let alpha_dummy_013 : Var := (freshVar (((Class.cv alpha_dummy_005)).fv) 1)
  let alpha_dummy_014 : Var := (freshVar (((Class.cv alpha_dummy_007)).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((Class.cv alpha_dummy_007)).fv) 1)
  let alpha_dummy_016 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_012) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_012) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_012)).fv) 0)
  let alpha_dummy_017 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_014) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_014)).fv) 0)
  let alpha_dummy_018 : Var :=
    (freshVar (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_019 : Var :=
    (freshVar (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_020 : Var :=
    (freshVar (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_021 : Var :=
    (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_022 : Var :=
    (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_023 : Var :=
    (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_024 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) 0)
  let alpha_dummy_025 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))).fv) 0)
  let alpha_dummy_026 : Var :=
    (freshVar (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_020)).fv) 0)
  let alpha_dummy_027 : Var :=
    (freshVar (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_023)).fv) 0)
  let alpha_dummy_028 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_019))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_020))).fv) 0)
  let alpha_dummy_029 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_022))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_023))).fv) 0)
  let alpha_dummy_030 : Var :=
    (freshVar (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_019)).fv) 0)
  let alpha_dummy_031 : Var :=
    (freshVar (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) 0)
  let alpha_dummy_032 : Var :=
    (freshVar (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_020)).fv) 0)
  let alpha_dummy_033 : Var :=
    (freshVar (((Class.cv alpha_dummy_023)).fv ∪ ((Class.cv alpha_dummy_023)).fv) 0)
  let alpha_dummy_034 : Var :=
    (freshVar (((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_035 : Var :=
    (freshVar (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv y)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv y)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_036 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_005)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_037 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_007)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_038 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_005))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_005))).fv) 0)
  let alpha_dummy_039 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_007))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_007))).fv) 0)
  let alpha_dummy_040 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_041 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1)
  let alpha_dummy_042 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0)
  let alpha_dummy_043 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1)
  let alpha_dummy_044 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_040
              (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_040)
                  (syn_cphi (Class.cv alpha_dummy_041))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_040)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_041)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_045 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_046 : Var :=
    (freshVar (((Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_040)
                (syn_cphi (Class.cv alpha_dummy_041)))))).fv ∪ ((Class.cab alpha_dummy_040
            (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_040)
                (syn_cphi (Class.cv alpha_dummy_041)))))).fv) 0)
  let alpha_dummy_047 : Var :=
    (freshVar (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv y)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cphi (Class.cv alpha_dummy_043)))))).fv ∪ ((Class.cab alpha_dummy_042
            (syn_wrex alpha_dummy_043 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cphi (Class.cv alpha_dummy_043)))))).fv) 0)
  let alpha_dummy_048 : Var := (freshVar (((Class.cv alpha_dummy_041)).fv) 0)
  let alpha_dummy_049 : Var := (freshVar (((Class.cv alpha_dummy_041)).fv) 1)
  let alpha_dummy_050 : Var := (freshVar (((Class.cv alpha_dummy_043)).fv) 0)
  let alpha_dummy_051 : Var := (freshVar (((Class.cv alpha_dummy_043)).fv) 1)
  let alpha_dummy_052 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_048) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_048) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_048)).fv) 0)
  let alpha_dummy_053 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_050) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_050)).fv) 0)
  let alpha_dummy_054 : Var :=
    (freshVar (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_055 : Var :=
    (freshVar (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_056 : Var :=
    (freshVar (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_057 : Var :=
    (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_058 : Var :=
    (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_059 : Var :=
    (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_060 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056))).fv) 0)
  let alpha_dummy_061 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))).fv) 0)
  let alpha_dummy_062 : Var :=
    (freshVar (((Class.cv alpha_dummy_055)).fv ∪ ((Class.cv alpha_dummy_056)).fv) 0)
  let alpha_dummy_063 : Var :=
    (freshVar (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_059)).fv) 0)
  let alpha_dummy_064 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_055))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_056))).fv) 0)
  let alpha_dummy_065 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_058))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_059))).fv) 0)
  let alpha_dummy_066 : Var :=
    (freshVar (((Class.cv alpha_dummy_055)).fv ∪ ((Class.cv alpha_dummy_055)).fv) 0)
  let alpha_dummy_067 : Var :=
    (freshVar (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_058)).fv) 0)
  let alpha_dummy_068 : Var :=
    (freshVar (((Class.cv alpha_dummy_056)).fv ∪ ((Class.cv alpha_dummy_056)).fv) 0)
  let alpha_dummy_069 : Var :=
    (freshVar (((Class.cv alpha_dummy_059)).fv ∪ ((Class.cv alpha_dummy_059)).fv) 0)
  let alpha_dummy_070 : Var :=
    (freshVar (((Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_040)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_041)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_040)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_041)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_071 : Var :=
    (freshVar (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_072 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_041)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_073 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_043)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_074 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_041))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_041))).fv) 0)
  let alpha_dummy_075 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_043))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_043))).fv) 0)
  have fresh_092 : alpha_dummy_000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have fresh_093 : alpha_dummy_001 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 1
  have fresh_095 :
    alpha_dummy_002 ∉
      (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
        ((syn_wbr (Class.cv alpha_dummy_001) A (Class.cv alpha_dummy_000))).fv) :=
    by
    exact
      freshVar_not_mem
        (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
          ((syn_wbr (Class.cv alpha_dummy_001) A (Class.cv alpha_dummy_000))).fv)
        0
  have fresh_096 :
    alpha_dummy_003 ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wbr (Class.cv y) A (Class.cv x))).fv) :=
    by
    exact
      freshVar_not_mem
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ((syn_wbr (Class.cv y) A (Class.cv x))).fv)
        0
  have support_mem_0000 :
    alpha_dummy_000 ∈
      (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
        ((syn_wbr (Class.cv alpha_dummy_001) A (Class.cv alpha_dummy_000))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    exact Finset.mem_singleton_self _
  have support_mem_0001 :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wbr (Class.cv y) A (Class.cv x))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    exact Finset.mem_singleton_self _
  have support_mem_0002 :
    alpha_dummy_001 ∈
      (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
        ((syn_wbr (Class.cv alpha_dummy_001) A (Class.cv alpha_dummy_000))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    right
    exact Finset.mem_singleton_self _
  have support_mem_0003 :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wbr (Class.cv y) A (Class.cv x))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    right
    exact Finset.mem_singleton_self _
  have support_mem_0004 :
    alpha_dummy_000 ∈
      (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 :
    alpha_dummy_000 ∈
      (((syn_ccompl (Class.cab alpha_dummy_004
              (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cphi (Class.cv alpha_dummy_005))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_001)
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
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0006 : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0007 :
    x ∈
      (((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_007))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alpha_dummy_000 ∈
      (((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cphi (Class.cv alpha_dummy_005)))))).fv ∪ ((Class.cab alpha_dummy_004
            (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cphi (Class.cv alpha_dummy_005)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0009 :
    x ∈
      (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cphi (Class.cv alpha_dummy_007)))))).fv ∪ ((Class.cab alpha_dummy_006
            (syn_wrex alpha_dummy_007 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cphi (Class.cv alpha_dummy_007)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0010 : alpha_dummy_005 ∈ (((Class.cv alpha_dummy_005)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0011 : alpha_dummy_007 ∈ (((Class.cv alpha_dummy_007)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
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
  have support_mem_0013 :
    alpha_dummy_014 ∈
      (((Wff.classMem (Class.cv alpha_dummy_014) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_014)).fv) :=
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
  have support_mem_0014 :
    alpha_dummy_012 ∈ (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alpha_dummy_019 ∈
      (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alpha_dummy_022 ∈
      (((syn_cnin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alpha_dummy_019 ∈
      (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_020)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alpha_dummy_022 ∈
      (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alpha_dummy_020 ∈
      (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alpha_dummy_023 ∈
      (((syn_cnin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 :
    alpha_dummy_020 ∈
      (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_020)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    alpha_dummy_023 ∈
      (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0024 :
    alpha_dummy_019 ∈
      (((syn_ccompl (Class.cv alpha_dummy_019))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_020))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    alpha_dummy_022 ∈
      (((syn_ccompl (Class.cv alpha_dummy_022))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0026 :
    alpha_dummy_019 ∈
      (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_019)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0027 :
    alpha_dummy_022 ∈
      (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0028 :
    alpha_dummy_020 ∈
      (((syn_ccompl (Class.cv alpha_dummy_019))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_020))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0029 :
    alpha_dummy_023 ∈
      (((syn_ccompl (Class.cv alpha_dummy_022))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0030 :
    alpha_dummy_020 ∈
      (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_020)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0031 :
    alpha_dummy_023 ∈
      (((Class.cv alpha_dummy_023)).fv ∪ ((Class.cv alpha_dummy_023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0032 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0033 :
    alpha_dummy_001 ∈
      (((syn_ccompl (Class.cab alpha_dummy_004
              (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_004)
                  (syn_cphi (Class.cv alpha_dummy_005))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_001)
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
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0034 : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0035 :
    y ∈
      (((syn_ccompl (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_007))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0036 :
    alpha_dummy_001 ∈
      (((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_004 (syn_wrex alpha_dummy_005 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_004)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_005)) (syn_csn (syn_c0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0037 :
    y ∈
      (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv y)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv y)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0038 :
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
  have support_mem_0039 :
    alpha_dummy_007 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_007)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0040 :
    alpha_dummy_005 ∈
      (((syn_cphi (Class.cv alpha_dummy_005))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_005))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0041 :
    alpha_dummy_007 ∈
      (((syn_cphi (Class.cv alpha_dummy_007))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_007))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0042 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0043 :
    alpha_dummy_001 ∈
      (((syn_ccompl (Class.cab alpha_dummy_040
              (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_040)
                  (syn_cphi (Class.cv alpha_dummy_041))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_040)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_041))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0044 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0045 :
    y ∈
      (((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_043))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0046 :
    alpha_dummy_001 ∈
      (((Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_040)
                (syn_cphi (Class.cv alpha_dummy_041)))))).fv ∪ ((Class.cab alpha_dummy_040
            (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_040)
                (syn_cphi (Class.cv alpha_dummy_041)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0047 :
    y ∈
      (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv y)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cphi (Class.cv alpha_dummy_043)))))).fv ∪ ((Class.cab alpha_dummy_042
            (syn_wrex alpha_dummy_043 (Class.cv y) (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cphi (Class.cv alpha_dummy_043)))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0048 : alpha_dummy_041 ∈ (((Class.cv alpha_dummy_041)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0049 : alpha_dummy_043 ∈ (((Class.cv alpha_dummy_043)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0050 :
    alpha_dummy_048 ∈
      (((Wff.classMem (Class.cv alpha_dummy_048) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_048) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_048)).fv) :=
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
  have support_mem_0051 :
    alpha_dummy_050 ∈
      (((Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_050) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_050)).fv) :=
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
  have support_mem_0052 :
    alpha_dummy_048 ∈ (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0053 :
    alpha_dummy_050 ∈ (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0054 :
    alpha_dummy_055 ∈
      (((syn_cnin (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0055 :
    alpha_dummy_058 ∈
      (((syn_cnin (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0056 :
    alpha_dummy_055 ∈
      (((Class.cv alpha_dummy_055)).fv ∪ ((Class.cv alpha_dummy_056)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0057 :
    alpha_dummy_058 ∈
      (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_059)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0058 :
    alpha_dummy_056 ∈
      (((syn_cnin (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0059 :
    alpha_dummy_059 ∈
      (((syn_cnin (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0060 :
    alpha_dummy_056 ∈
      (((Class.cv alpha_dummy_055)).fv ∪ ((Class.cv alpha_dummy_056)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0061 :
    alpha_dummy_059 ∈
      (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_059)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0062 :
    alpha_dummy_055 ∈
      (((syn_ccompl (Class.cv alpha_dummy_055))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_056))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0063 :
    alpha_dummy_058 ∈
      (((syn_ccompl (Class.cv alpha_dummy_058))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_059))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0064 :
    alpha_dummy_055 ∈
      (((Class.cv alpha_dummy_055)).fv ∪ ((Class.cv alpha_dummy_055)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0065 :
    alpha_dummy_058 ∈
      (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_058)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0066 :
    alpha_dummy_056 ∈
      (((syn_ccompl (Class.cv alpha_dummy_055))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_056))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0067 :
    alpha_dummy_059 ∈
      (((syn_ccompl (Class.cv alpha_dummy_058))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_059))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0068 :
    alpha_dummy_056 ∈
      (((Class.cv alpha_dummy_056)).fv ∪ ((Class.cv alpha_dummy_056)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0069 :
    alpha_dummy_059 ∈
      (((Class.cv alpha_dummy_059)).fv ∪ ((Class.cv alpha_dummy_059)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0070 :
    alpha_dummy_000 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0071 :
    alpha_dummy_000 ∈
      (((syn_ccompl (Class.cab alpha_dummy_040
              (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_040)
                  (syn_cphi (Class.cv alpha_dummy_041))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_040)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_041))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0072 : x ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0073 :
    x ∈
      (((syn_ccompl (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv y)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_043))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0074 :
    alpha_dummy_000 ∈
      (((Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_040)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_041)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_040 (syn_wrex alpha_dummy_041 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_040)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_041)) (syn_csn (syn_c0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0075 :
    x ∈
      (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0076 :
    alpha_dummy_041 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_041)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0077 :
    alpha_dummy_043 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_043)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0078 :
    alpha_dummy_041 ∈
      (((syn_cphi (Class.cv alpha_dummy_041))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_041))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0079 :
    alpha_dummy_043 ∈
      (((syn_cphi (Class.cv alpha_dummy_043))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_043))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have wpp_notmem_0000 : alpha_dummy_002 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0001 : alpha_dummy_003 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0002 : alpha_dummy_000 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0003 : x ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0004 : alpha_dummy_001 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0005 : y ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0006 : alpha_dummy_008 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0007 : alpha_dummy_009 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0008 : alpha_dummy_010 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0009 : alpha_dummy_011 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0010 : alpha_dummy_004 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0011 : alpha_dummy_006 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0012 : alpha_dummy_005 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0013 : alpha_dummy_007 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0014 : alpha_dummy_013 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0015 : alpha_dummy_015 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0016 : alpha_dummy_012 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alpha_dummy_014 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alpha_dummy_016 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alpha_dummy_017 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alpha_dummy_018 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alpha_dummy_021 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alpha_dummy_019 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : alpha_dummy_022 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alpha_dummy_020 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alpha_dummy_023 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0000 :
    TReflOn
      [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
        (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
        (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c1c)).fv :=
    by
    intro u hu
    exact
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
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu))
                                (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have wpp_notmem_0026 : alpha_dummy_002 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0027 : alpha_dummy_003 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0028 : alpha_dummy_000 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0029 : x ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0030 : alpha_dummy_001 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0031 : y ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0032 : alpha_dummy_008 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0033 : alpha_dummy_009 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0034 : alpha_dummy_010 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0035 : alpha_dummy_011 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0036 : alpha_dummy_004 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0037 : alpha_dummy_006 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0038 : alpha_dummy_005 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0039 : alpha_dummy_007 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0040 : alpha_dummy_013 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0041 : alpha_dummy_015 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0042 : alpha_dummy_012 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0043 : alpha_dummy_014 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0044 : alpha_dummy_016 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alpha_dummy_017 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alpha_dummy_018 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alpha_dummy_021 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0048 : alpha_dummy_019 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0049 : alpha_dummy_022 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0050 : alpha_dummy_020 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0051 : alpha_dummy_023 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
        (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
        (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
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
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
                                (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
        (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
        (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_018)
            (syn_cun (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_021)
            (syn_cun (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
            (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
            (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
            (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
            (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_008, alpha_dummy_009),
            (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
          (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0052 : alpha_dummy_002 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0053 : alpha_dummy_003 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0054 : alpha_dummy_000 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0055 : x ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0056 : alpha_dummy_001 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0057 : y ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0058 : alpha_dummy_008 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0059 : alpha_dummy_009 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0060 : alpha_dummy_010 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0061 : alpha_dummy_011 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0062 : alpha_dummy_004 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0063 : alpha_dummy_006 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0064 : alpha_dummy_005 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0065 : alpha_dummy_007 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0066 : alpha_dummy_013 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0067 : alpha_dummy_015 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0068 : alpha_dummy_012 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0069 : alpha_dummy_014 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0070 : alpha_dummy_016 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0071 : alpha_dummy_017 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alpha_dummy_016, alpha_dummy_017), (alpha_dummy_012, alpha_dummy_014),
        (alpha_dummy_013, alpha_dummy_015), (alpha_dummy_005, alpha_dummy_007),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_010, alpha_dummy_011),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0070) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0071) (h_eq ▸ hu))
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
                          (TAlphaVar.free (by simp) (by simp))))))))))))
  have split_alpha_0001 :
    TAlphaWff
      [(alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_000)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_004) (syn_cphi (Class.cv alpha_dummy_005)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_007) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                  (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
                    (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) (by decide))
              (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alpha_dummy_005)).fv) (by decide))
                      (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
        (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
        (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg split_alpha_0000)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_016, alpha_dummy_017),
                                (alpha_dummy_012, alpha_dummy_014),
                                (alpha_dummy_013, alpha_dummy_015),
                                (alpha_dummy_005, alpha_dummy_007),
                                (alpha_dummy_004, alpha_dummy_006),
                                (alpha_dummy_010, alpha_dummy_011),
                                (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_016, alpha_dummy_017),
                                (alpha_dummy_012, alpha_dummy_014),
                                (alpha_dummy_013, alpha_dummy_015),
                                (alpha_dummy_005, alpha_dummy_007),
                                (alpha_dummy_004, alpha_dummy_006),
                                (alpha_dummy_010, alpha_dummy_011),
                                (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0072 : alpha_dummy_034 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0073 : alpha_dummy_035 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0074 : alpha_dummy_036 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0075 : alpha_dummy_037 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0076 : alpha_dummy_038 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0077 : alpha_dummy_039 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn
      [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
        (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
        (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
        (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c1c)).fv :=
    by
    intro u hu
    exact
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0012) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0013) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0010) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0011) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0006) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0007) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu))
                                    (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have wpp_notmem_0078 : alpha_dummy_034 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0079 : alpha_dummy_035 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0080 : alpha_dummy_036 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0081 : alpha_dummy_037 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0082 : alpha_dummy_038 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0083 : alpha_dummy_039 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0004 :
    TReflOn
      [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
        (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
        (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
        (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0038) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0039) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0036) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0037) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0032) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0033) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
                                    (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have split_alpha_0002 :
    TAlphaWff
      [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
        (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
        (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
        (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_018)
            (syn_cun (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_021)
            (syn_cun (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
            (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
            (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
            (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_036, alpha_dummy_037),
            (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
            (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_008, alpha_dummy_009),
            (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
          (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_012)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0084 : alpha_dummy_034 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alpha_dummy_035 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alpha_dummy_036 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alpha_dummy_037 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0088 : alpha_dummy_038 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0089 : alpha_dummy_039 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0005 :
    TReflOn
      [(alpha_dummy_016, alpha_dummy_017), (alpha_dummy_012, alpha_dummy_014),
        (alpha_dummy_013, alpha_dummy_015), (alpha_dummy_038, alpha_dummy_039),
        (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_005, alpha_dummy_007),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0070) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0071) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0068) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0069) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0066) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0067) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0064) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0065) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0062) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0063) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have split_alpha_0003 :
    TAlphaWff
      [(alpha_dummy_038, alpha_dummy_039), (alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_038) (syn_cphi (Class.cv alpha_dummy_005)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_038)
            (syn_cphi (Class.cv alpha_dummy_005)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_039) (syn_cphi (Class.cv alpha_dummy_007)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_039)
            (syn_cphi (Class.cv alpha_dummy_007))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_005)).fv) (by decide))
                    (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_020, alpha_dummy_023),
        (alpha_dummy_019, alpha_dummy_022), (alpha_dummy_018, alpha_dummy_021),
        (alpha_dummy_016, alpha_dummy_017), (alpha_dummy_012, alpha_dummy_014),
        (alpha_dummy_013, alpha_dummy_015), (alpha_dummy_038, alpha_dummy_039),
        (alpha_dummy_036, alpha_dummy_037), (alpha_dummy_005, alpha_dummy_007),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_002, alpha_dummy_003)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg split_alpha_0002))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_016, alpha_dummy_017),
                              (alpha_dummy_012, alpha_dummy_014),
                              (alpha_dummy_013, alpha_dummy_015),
                              (alpha_dummy_038, alpha_dummy_039),
                              (alpha_dummy_036, alpha_dummy_037),
                              (alpha_dummy_005, alpha_dummy_007),
                              (alpha_dummy_004, alpha_dummy_006),
                              (alpha_dummy_034, alpha_dummy_035),
                              (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y),
                              (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_016, alpha_dummy_017),
                              (alpha_dummy_012, alpha_dummy_014),
                              (alpha_dummy_013, alpha_dummy_015),
                              (alpha_dummy_038, alpha_dummy_039),
                              (alpha_dummy_036, alpha_dummy_037),
                              (alpha_dummy_005, alpha_dummy_007),
                              (alpha_dummy_004, alpha_dummy_006),
                              (alpha_dummy_034, alpha_dummy_035),
                              (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y),
                              (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 1)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alpha_dummy_005)).fv) (by decide))
                      (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [(alpha_dummy_020, alpha_dummy_023), (alpha_dummy_019, alpha_dummy_022),
        (alpha_dummy_018, alpha_dummy_021), (alpha_dummy_016, alpha_dummy_017),
        (alpha_dummy_012, alpha_dummy_014), (alpha_dummy_013, alpha_dummy_015),
        (alpha_dummy_038, alpha_dummy_039), (alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg split_alpha_0002)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_016, alpha_dummy_017),
                                (alpha_dummy_012, alpha_dummy_014),
                                (alpha_dummy_013, alpha_dummy_015),
                                (alpha_dummy_038, alpha_dummy_039),
                                (alpha_dummy_036, alpha_dummy_037),
                                (alpha_dummy_005, alpha_dummy_007),
                                (alpha_dummy_004, alpha_dummy_006),
                                (alpha_dummy_034, alpha_dummy_035),
                                (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_016, alpha_dummy_017),
                                (alpha_dummy_012, alpha_dummy_014),
                                (alpha_dummy_013, alpha_dummy_015),
                                (alpha_dummy_038, alpha_dummy_039),
                                (alpha_dummy_036, alpha_dummy_037),
                                (alpha_dummy_005, alpha_dummy_007),
                                (alpha_dummy_004, alpha_dummy_006),
                                (alpha_dummy_034, alpha_dummy_035),
                                (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0090 : alpha_dummy_002 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0091 : alpha_dummy_003 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
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
  have wpp_notmem_0096 : alpha_dummy_008 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0097 : alpha_dummy_009 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0098 : alpha_dummy_034 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0099 : alpha_dummy_035 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0100 : alpha_dummy_004 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0101 : alpha_dummy_006 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0102 : alpha_dummy_005 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0103 : alpha_dummy_007 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0104 : alpha_dummy_036 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0105 : alpha_dummy_037 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_refl_0006 :
    TReflOn
      [(alpha_dummy_036, alpha_dummy_037), (alpha_dummy_005, alpha_dummy_007),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_034, alpha_dummy_035),
        (alpha_dummy_008, alpha_dummy_009), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0104) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0105) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0102) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0103) (h_eq ▸ hu))
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
                      (TAlphaVar.free (by simp) (by simp))))))))))
  have split_alpha_0004 :
    TAlphaWff
      [(alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.classEq (Class.cv alpha_dummy_002)
        (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))
      (Wff.classEq (Class.cv alpha_dummy_003) (syn_cop (Class.cv x) (Class.cv y))) :=
    (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)))
          (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
            (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0033 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_000)).fv ∪
                                      ((Class.cv alpha_dummy_001)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0033 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_000)).fv ∪
                                      ((Class.cv alpha_dummy_001)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_036, alpha_dummy_037),
        (alpha_dummy_005, alpha_dummy_007), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_034, alpha_dummy_035), (alpha_dummy_008, alpha_dummy_009),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))))))))))
  have wpp_notmem_0106 : alpha_dummy_044 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0107 : alpha_dummy_045 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0108 : alpha_dummy_046 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0109 : alpha_dummy_047 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0110 : alpha_dummy_040 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0111 : alpha_dummy_042 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0112 : alpha_dummy_041 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0113 : alpha_dummy_043 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0114 : alpha_dummy_049 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0115 : alpha_dummy_051 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0116 : alpha_dummy_048 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0117 : alpha_dummy_050 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0118 : alpha_dummy_052 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0119 : alpha_dummy_053 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0120 : alpha_dummy_054 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0121 : alpha_dummy_057 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0122 : alpha_dummy_055 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0123 : alpha_dummy_058 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0124 : alpha_dummy_056 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0125 : alpha_dummy_059 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0007 :
    TReflOn
      [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
        (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
        (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c1c)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0124) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0125) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0122) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0123) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0120) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0121) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0118) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0119) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0116) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0117) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0114) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0115) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0112) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0113) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0110) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0111) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0108) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0109) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu))
                                (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have wpp_notmem_0126 : alpha_dummy_044 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0127 : alpha_dummy_045 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0128 : alpha_dummy_046 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0129 : alpha_dummy_047 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0130 : alpha_dummy_040 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0131 : alpha_dummy_042 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0132 : alpha_dummy_041 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0133 : alpha_dummy_043 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0134 : alpha_dummy_049 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0135 : alpha_dummy_051 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0136 : alpha_dummy_048 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0137 : alpha_dummy_050 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0138 : alpha_dummy_052 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0139 : alpha_dummy_053 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0140 : alpha_dummy_054 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0141 : alpha_dummy_057 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0142 : alpha_dummy_055 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0143 : alpha_dummy_058 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0144 : alpha_dummy_056 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0145 : alpha_dummy_059 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0008 :
    TReflOn
      [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
        (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
        (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c0)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0144) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0145) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0142) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0143) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0140) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0141) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0138) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0139) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0136) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0137) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0134) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0135) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0132) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0133) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0130) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0131) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0128) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0129) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0126) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0127) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
                                (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have split_alpha_0005 :
    TAlphaWff
      [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
        (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
        (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_054)
            (syn_cun (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_057)
            (syn_cun (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
            (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
            (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
            (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
            (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_044, alpha_dummy_045),
            (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
          (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0146 : alpha_dummy_044 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0147 : alpha_dummy_045 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0148 : alpha_dummy_046 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0149 : alpha_dummy_047 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0150 : alpha_dummy_040 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0151 : alpha_dummy_042 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0152 : alpha_dummy_041 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0153 : alpha_dummy_043 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0154 : alpha_dummy_049 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0155 : alpha_dummy_051 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0156 : alpha_dummy_048 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0157 : alpha_dummy_050 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0158 : alpha_dummy_052 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0159 : alpha_dummy_053 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0009 :
    TReflOn
      [(alpha_dummy_052, alpha_dummy_053), (alpha_dummy_048, alpha_dummy_050),
        (alpha_dummy_049, alpha_dummy_051), (alpha_dummy_041, alpha_dummy_043),
        (alpha_dummy_040, alpha_dummy_042), (alpha_dummy_046, alpha_dummy_047),
        (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0158) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0159) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0156) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0157) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0154) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0155) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0152) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0153) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0150) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0151) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0148) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0149) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0146) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0147) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                          (TAlphaVar.free (by simp) (by simp))))))))))))
  have split_alpha_0006 :
    TAlphaWff
      [(alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_041) (Class.cv alpha_dummy_001)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_040) (syn_cphi (Class.cv alpha_dummy_041)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_043) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0))
                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective
                (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide))
              (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 1))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alpha_dummy_041)).fv) (by decide))
                      (freshVar_injective (((Class.cv alpha_dummy_043)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0053 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0053 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
        (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
        (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_046, alpha_dummy_047), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg split_alpha_0005)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_052, alpha_dummy_053),
                                (alpha_dummy_048, alpha_dummy_050),
                                (alpha_dummy_049, alpha_dummy_051),
                                (alpha_dummy_041, alpha_dummy_043),
                                (alpha_dummy_040, alpha_dummy_042),
                                (alpha_dummy_046, alpha_dummy_047),
                                (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_052, alpha_dummy_053),
                                (alpha_dummy_048, alpha_dummy_050),
                                (alpha_dummy_049, alpha_dummy_051),
                                (alpha_dummy_041, alpha_dummy_043),
                                (alpha_dummy_040, alpha_dummy_042),
                                (alpha_dummy_046, alpha_dummy_047),
                                (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0160 : alpha_dummy_070 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0161 : alpha_dummy_071 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0162 : alpha_dummy_072 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0163 : alpha_dummy_073 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0164 : alpha_dummy_074 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0165 : alpha_dummy_075 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0010 :
    TReflOn
      [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
        (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
        (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
        (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_072, alpha_dummy_073),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_070, alpha_dummy_071), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c1c)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0124) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0125) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0122) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0123) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0120) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0121) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0118) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0119) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0116) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0117) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0114) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0115) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0164) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0165) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0162) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0163) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0112) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0113) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0110) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0111) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0160) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0161) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0004) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0005) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0002) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0003) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0000) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0001) (h_eq ▸ hu))
                                    (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have wpp_notmem_0166 : alpha_dummy_070 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0167 : alpha_dummy_071 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0168 : alpha_dummy_072 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0169 : alpha_dummy_073 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0170 : alpha_dummy_074 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0171 : alpha_dummy_075 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0011 :
    TReflOn
      [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
        (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
        (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
        (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_072, alpha_dummy_073),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_070, alpha_dummy_071), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      ((syn_c0)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0144) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0145) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0142) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0143) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0140) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0141) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0138) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0139) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0136) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0137) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0134) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0135) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0170) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0171) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0168) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0169) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0132) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0133) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0130) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0131) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0166) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0167) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0126) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0127) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0026) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0027) (h_eq ▸ hu))
                                    (TAlphaVar.free (by simp) (by simp)))))))))))))))))
  have split_alpha_0007 :
    TAlphaWff
      [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
        (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
        (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
        (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_072, alpha_dummy_073),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_070, alpha_dummy_071), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_054)
            (syn_cun (Class.cv alpha_dummy_055) (Class.cv alpha_dummy_056)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_057)
            (syn_cun (Class.cv alpha_dummy_058) (Class.cv alpha_dummy_059))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
            (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
            (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
            (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_072, alpha_dummy_073),
            (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
            (alpha_dummy_070, alpha_dummy_071), (alpha_dummy_044, alpha_dummy_045),
            (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
          (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0063 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_048)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have wpp_notmem_0172 : alpha_dummy_070 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0173 : alpha_dummy_071 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0174 : alpha_dummy_072 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0175 : alpha_dummy_073 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0176 : alpha_dummy_074 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0177 : alpha_dummy_075 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0012 :
    TReflOn
      [(alpha_dummy_052, alpha_dummy_053), (alpha_dummy_048, alpha_dummy_050),
        (alpha_dummy_049, alpha_dummy_051), (alpha_dummy_074, alpha_dummy_075),
        (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_041, alpha_dummy_043),
        (alpha_dummy_040, alpha_dummy_042), (alpha_dummy_070, alpha_dummy_071),
        (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0158) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0159) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0156) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0157) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0154) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0155) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0176) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0177) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0174) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0175) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0152) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0153) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0150) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0151) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0172) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0173) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0146) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0147) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0054) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0055) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                              (TAlphaVar.free (by simp) (by simp))))))))))))))
  have split_alpha_0008 :
    TAlphaWff
      [(alpha_dummy_074, alpha_dummy_075), (alpha_dummy_072, alpha_dummy_073),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_070, alpha_dummy_071), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_074) (syn_cphi (Class.cv alpha_dummy_041)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_074)
            (syn_cphi (Class.cv alpha_dummy_041)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_075) (syn_cphi (Class.cv alpha_dummy_043)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_075)
            (syn_cphi (Class.cv alpha_dummy_043))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0079 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0077 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_041)).fv) (by decide))
                    (freshVar_injective (((Class.cv alpha_dummy_043)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0053 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_056, alpha_dummy_059),
        (alpha_dummy_055, alpha_dummy_058), (alpha_dummy_054, alpha_dummy_057),
        (alpha_dummy_052, alpha_dummy_053), (alpha_dummy_048, alpha_dummy_050),
        (alpha_dummy_049, alpha_dummy_051), (alpha_dummy_074, alpha_dummy_075),
        (alpha_dummy_072, alpha_dummy_073), (alpha_dummy_041, alpha_dummy_043),
        (alpha_dummy_040, alpha_dummy_042), (alpha_dummy_070, alpha_dummy_071),
        (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_002, alpha_dummy_003)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg split_alpha_0007))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_052, alpha_dummy_053),
                              (alpha_dummy_048, alpha_dummy_050),
                              (alpha_dummy_049, alpha_dummy_051),
                              (alpha_dummy_074, alpha_dummy_075),
                              (alpha_dummy_072, alpha_dummy_073),
                              (alpha_dummy_041, alpha_dummy_043),
                              (alpha_dummy_040, alpha_dummy_042),
                              (alpha_dummy_070, alpha_dummy_071),
                              (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y),
                              (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_052, alpha_dummy_053),
                              (alpha_dummy_048, alpha_dummy_050),
                              (alpha_dummy_049, alpha_dummy_051),
                              (alpha_dummy_074, alpha_dummy_075),
                              (alpha_dummy_072, alpha_dummy_073),
                              (alpha_dummy_041, alpha_dummy_043),
                              (alpha_dummy_040, alpha_dummy_042),
                              (alpha_dummy_070, alpha_dummy_071),
                              (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y),
                              (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 1)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0079 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0077 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alpha_dummy_041)).fv) (by decide))
                      (freshVar_injective (((Class.cv alpha_dummy_043)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 1)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0053 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0053 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed
        [(alpha_dummy_056, alpha_dummy_059), (alpha_dummy_055, alpha_dummy_058),
        (alpha_dummy_054, alpha_dummy_057), (alpha_dummy_052, alpha_dummy_053),
        (alpha_dummy_048, alpha_dummy_050), (alpha_dummy_049, alpha_dummy_051),
        (alpha_dummy_074, alpha_dummy_075), (alpha_dummy_072, alpha_dummy_073),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_070, alpha_dummy_071), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg split_alpha_0007)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_052, alpha_dummy_053),
                                (alpha_dummy_048, alpha_dummy_050),
                                (alpha_dummy_049, alpha_dummy_051),
                                (alpha_dummy_074, alpha_dummy_075),
                                (alpha_dummy_072, alpha_dummy_073),
                                (alpha_dummy_041, alpha_dummy_043),
                                (alpha_dummy_040, alpha_dummy_042),
                                (alpha_dummy_070, alpha_dummy_071),
                                (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_052, alpha_dummy_053),
                                (alpha_dummy_048, alpha_dummy_050),
                                (alpha_dummy_049, alpha_dummy_051),
                                (alpha_dummy_074, alpha_dummy_075),
                                (alpha_dummy_072, alpha_dummy_073),
                                (alpha_dummy_041, alpha_dummy_043),
                                (alpha_dummy_040, alpha_dummy_042),
                                (alpha_dummy_070, alpha_dummy_071),
                                (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y),
                                (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0178 : alpha_dummy_044 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0179 : alpha_dummy_045 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0180 : alpha_dummy_070 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0181 : alpha_dummy_071 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0182 : alpha_dummy_040 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0183 : alpha_dummy_042 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0184 : alpha_dummy_041 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0185 : alpha_dummy_043 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0186 : alpha_dummy_072 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0187 : alpha_dummy_073 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_refl_0013 :
    TReflOn
      [(alpha_dummy_072, alpha_dummy_073), (alpha_dummy_041, alpha_dummy_043),
        (alpha_dummy_040, alpha_dummy_042), (alpha_dummy_070, alpha_dummy_071),
        (alpha_dummy_044, alpha_dummy_045), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_002, alpha_dummy_003)]
      ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0186) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0187) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0184) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0185) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0182) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0183) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0180) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0181) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0178) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0179) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0094) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0095) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu))
                      (TAlphaVar.free (by simp) (by simp))))))))))
  have focused_notmem_0000 : alpha_dummy_002 ∉ A.fv :=
    by
    change
      freshVar
          (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
            ((syn_wbr (Class.cv alpha_dummy_001) A (Class.cv alpha_dummy_000))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wbr (Class.cv alpha_dummy_001) A (Class.cv alpha_dummy_000)).symm ▸
              (Finset.mem_union_right _ (hu)))))
  have wpp_notmem_0188 : alpha_dummy_002 ∉ (A).fv := by exact focused_notmem_0000
  have focused_notmem_0001 : alpha_dummy_003 ∉ A.fv :=
    by
    change
      freshVar
          (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ((syn_wbr (Class.cv y) A (Class.cv x))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_wbr (Class.cv y) A (Class.cv x)).symm ▸
              (Finset.mem_union_right _ (hu)))))
  have wpp_notmem_0189 : alpha_dummy_003 ∉ (A).fv := by exact focused_notmem_0001
  have focused_notmem_0002 : alpha_dummy_000 ∉ A.fv :=
    by
    change freshVar ((A).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => hu)
  have wpp_notmem_0190 : alpha_dummy_000 ∉ (A).fv := by exact focused_notmem_0002
  have wpp_notmem_0191 : x ∉ (A).fv := by exact dv_A_x
  have focused_notmem_0003 : alpha_dummy_001 ∉ A.fv :=
    by
    change freshVar ((A).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => hu)
  have wpp_notmem_0192 : alpha_dummy_001 ∉ (A).fv := by exact focused_notmem_0003
  have wpp_notmem_0193 : y ∉ (A).fv := by exact dv_A_y
  have wpp_refl_0014 :
    TReflOn
      [(alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (A).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0192) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0193) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0190) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0191) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0188) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0189) (h_eq ▸ hu)) (TAlphaVar.free (by simp) (by simp)))))
  have split_alpha_0009 :
    TAlphaWff
      [(alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
      (Wff.classMem (syn_cop (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)) A)
      (Wff.classMem (syn_cop (Class.cv y) (Class.cv x)) A) :=
    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg split_alpha_0006))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg split_alpha_0006))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0075 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0071 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0073 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪
                                      ((Class.cv alpha_dummy_000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg split_alpha_0008))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_072, alpha_dummy_073),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_070, alpha_dummy_071), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0075 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0071 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0073 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪
                                      ((Class.cv alpha_dummy_000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg split_alpha_0008))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_072, alpha_dummy_073),
        (alpha_dummy_041, alpha_dummy_043), (alpha_dummy_040, alpha_dummy_042),
        (alpha_dummy_070, alpha_dummy_071), (alpha_dummy_044, alpha_dummy_045),
        (alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))
      (TAlphaClass.refl_of_reflOn
        [(alpha_dummy_001, y), (alpha_dummy_000, x), (alpha_dummy_002, alpha_dummy_003)] A
        wpp_refl_0014))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj split_alpha_0004 split_alpha_0009))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
