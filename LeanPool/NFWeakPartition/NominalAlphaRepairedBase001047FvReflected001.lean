/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001047FvReflected001. -/


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
noncomputable def nominal_df_fv (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.classEq (syn_cfv F A) (syn_cio x (syn_wbr A F (.cv x)))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((F).fv ∪ (A).fv) 0)
  let alpha_dummy_001 : Var :=
    (freshVar
      (({ alpha_dummy_000 } : Finset Var) ∪ ((syn_wbr A F (Class.cv alpha_dummy_000))).fv) 0)
  let alpha_dummy_002 : Var :=
    (freshVar (({ x } : Finset Var) ∪ ((syn_wbr A F (Class.cv x))).fv) 0)
  let alpha_dummy_003 : Var :=
    (freshVar (((Class.cab alpha_dummy_001 (Wff.classEq
            (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
            (syn_csn (Class.cv alpha_dummy_001))))).fv) 0)
  let alpha_dummy_004 : Var :=
    (freshVar (((Class.cab alpha_dummy_001 (Wff.classEq
            (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
            (syn_csn (Class.cv alpha_dummy_001))))).fv) 1)
  let alpha_dummy_005 : Var :=
    (freshVar (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
            (syn_csn (Class.cv alpha_dummy_002))))).fv) 0)
  let alpha_dummy_006 : Var :=
    (freshVar (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
            (syn_csn (Class.cv alpha_dummy_002))))).fv) 1)
  let alpha_dummy_007 : Var := (freshVar ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_008 : Var := (freshVar ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1)
  let alpha_dummy_009 : Var := (freshVar ((A).fv ∪ ((Class.cv x)).fv) 0)
  let alpha_dummy_010 : Var := (freshVar ((A).fv ∪ ((Class.cv x)).fv) 1)
  let alpha_dummy_011 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
                (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cphi (Class.cv alpha_dummy_008))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_008)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_012 : Var :=
    (freshVar (((syn_ccompl (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
                (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cphi (Class.cv alpha_dummy_010))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_010)) (syn_csn (syn_c0c)))))))).fv)
      0)
  let alpha_dummy_013 : Var :=
    (freshVar (((Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
              (Wff.classEq (Class.cv alpha_dummy_007)
                (syn_cphi (Class.cv alpha_dummy_008)))))).fv ∪ ((Class.cab alpha_dummy_007
            (syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                (syn_cphi (Class.cv alpha_dummy_008)))))).fv) 0)
  let alpha_dummy_014 : Var :=
    (freshVar (((Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
              (Wff.classEq (Class.cv alpha_dummy_009)
                (syn_cphi (Class.cv alpha_dummy_010)))))).fv ∪ ((Class.cab alpha_dummy_009
            (syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                (syn_cphi (Class.cv alpha_dummy_010)))))).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((Class.cv alpha_dummy_008)).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((Class.cv alpha_dummy_008)).fv) 1)
  let alpha_dummy_017 : Var := (freshVar (((Class.cv alpha_dummy_010)).fv) 0)
  let alpha_dummy_018 : Var := (freshVar (((Class.cv alpha_dummy_010)).fv) 1)
  let alpha_dummy_019 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_015) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_015) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_015)).fv) 0)
  let alpha_dummy_020 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_017) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_017) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_017)).fv) 0)
  let alpha_dummy_021 : Var :=
    (freshVar (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_022 : Var :=
    (freshVar (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_023 : Var :=
    (freshVar (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_024 : Var :=
    (freshVar (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_025 : Var :=
    (freshVar (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_026 : Var :=
    (freshVar (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_027 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))).fv) 0)
  let alpha_dummy_028 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))).fv) 0)
  let alpha_dummy_029 : Var :=
    (freshVar (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_023)).fv) 0)
  let alpha_dummy_030 : Var :=
    (freshVar (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_026)).fv) 0)
  let alpha_dummy_031 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_022))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_023))).fv) 0)
  let alpha_dummy_032 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_025))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_026))).fv) 0)
  let alpha_dummy_033 : Var :=
    (freshVar (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) 0)
  let alpha_dummy_034 : Var :=
    (freshVar (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_025)).fv) 0)
  let alpha_dummy_035 : Var :=
    (freshVar (((Class.cv alpha_dummy_023)).fv ∪ ((Class.cv alpha_dummy_023)).fv) 0)
  let alpha_dummy_036 : Var :=
    (freshVar (((Class.cv alpha_dummy_026)).fv ∪ ((Class.cv alpha_dummy_026)).fv) 0)
  let alpha_dummy_037 : Var :=
    (freshVar (((Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_007)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_008)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_007)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_008)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_038 : Var :=
    (freshVar (((Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_009)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_010)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_009)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_010)) (syn_csn (syn_c0c))))))).fv) 0)
  let alpha_dummy_039 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_008)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_040 : Var :=
    (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_010)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)
  let alpha_dummy_041 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_008))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_008))).fv) 0)
  let alpha_dummy_042 : Var :=
    (freshVar (((syn_cphi (Class.cv alpha_dummy_010))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_010))).fv) 0)
  let alpha_dummy_043 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_044 : Var := (freshVar (((Class.cv alpha_dummy_002)).fv) 0)
  have fresh_000 :
    alpha_dummy_003 ∉
      (((Class.cab alpha_dummy_001 (Wff.classEq
            (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
            (syn_csn (Class.cv alpha_dummy_001))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alpha_dummy_001 (Wff.classEq
              (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
              (syn_csn (Class.cv alpha_dummy_001))))).fv)
        0
  have fresh_001 :
    alpha_dummy_004 ∉
      (((Class.cab alpha_dummy_001 (Wff.classEq
            (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
            (syn_csn (Class.cv alpha_dummy_001))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alpha_dummy_001 (Wff.classEq
              (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
              (syn_csn (Class.cv alpha_dummy_001))))).fv)
        1
  have fresh_003 :
    alpha_dummy_005 ∉
      (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
            (syn_csn (Class.cv alpha_dummy_002))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
              (syn_csn (Class.cv alpha_dummy_002))))).fv)
        0
  have fresh_004 :
    alpha_dummy_006 ∉
      (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
            (syn_csn (Class.cv alpha_dummy_002))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
              (syn_csn (Class.cv alpha_dummy_002))))).fv)
        1
  have fresh_007 :
    alpha_dummy_013 ∉
      (((Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
              (Wff.classEq (Class.cv alpha_dummy_007)
                (syn_cphi (Class.cv alpha_dummy_008)))))).fv ∪ ((Class.cab alpha_dummy_007
            (syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                (syn_cphi (Class.cv alpha_dummy_008)))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
                (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cphi (Class.cv alpha_dummy_008)))))).fv ∪ ((Class.cab alpha_dummy_007
              (syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cphi (Class.cv alpha_dummy_008)))))).fv)
        0
  have fresh_009 :
    alpha_dummy_014 ∉
      (((Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
              (Wff.classEq (Class.cv alpha_dummy_009)
                (syn_cphi (Class.cv alpha_dummy_010)))))).fv ∪ ((Class.cab alpha_dummy_009
            (syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                (syn_cphi (Class.cv alpha_dummy_010)))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
                (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cphi (Class.cv alpha_dummy_010)))))).fv ∪ ((Class.cab alpha_dummy_009
              (syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cphi (Class.cv alpha_dummy_010)))))).fv)
        0
  have fresh_038 :
    alpha_dummy_011 ∉
      (((syn_ccompl (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
                (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cphi (Class.cv alpha_dummy_008))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_008))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_ccompl (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
                  (Wff.classEq (Class.cv alpha_dummy_007)
                    (syn_cphi (Class.cv alpha_dummy_008))))))).fv ∪ ((syn_ccompl
              (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
                  (Wff.classEq (Class.cv alpha_dummy_007)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_008)) (syn_csn (syn_c0c)))))))).fv)
        0
  have fresh_039 :
    alpha_dummy_012 ∉
      (((syn_ccompl (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
                (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cphi (Class.cv alpha_dummy_010))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_010))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_ccompl (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
                  (Wff.classEq (Class.cv alpha_dummy_009)
                    (syn_cphi (Class.cv alpha_dummy_010))))))).fv ∪ ((syn_ccompl
              (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
                  (Wff.classEq (Class.cv alpha_dummy_009)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_010)) (syn_csn (syn_c0c)))))))).fv)
        0
  have fresh_048 : alpha_dummy_007 ∉ ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0
  have fresh_049 : alpha_dummy_008 ∉ ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1
  have fresh_051 : alpha_dummy_009 ∉ ((A).fv ∪ ((Class.cv x)).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ((Class.cv x)).fv) 0
  have fresh_052 : alpha_dummy_010 ∉ ((A).fv ∪ ((Class.cv x)).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ((Class.cv x)).fv) 1
  have fresh_054 : alpha_dummy_000 ∉ ((F).fv ∪ (A).fv) := by
    exact freshVar_not_mem ((F).fv ∪ (A).fv) 0
  have fresh_055 :
    alpha_dummy_001 ∉
      (({ alpha_dummy_000 } : Finset Var) ∪ ((syn_wbr A F (Class.cv alpha_dummy_000))).fv) :=
    by
    exact
      freshVar_not_mem
        (({ alpha_dummy_000 } : Finset Var) ∪ ((syn_wbr A F (Class.cv alpha_dummy_000))).fv)
        0
  have fresh_056 :
    alpha_dummy_002 ∉ (({ x } : Finset Var) ∪ ((syn_wbr A F (Class.cv x))).fv) := by
    exact freshVar_not_mem (({ x } : Finset Var) ∪ ((syn_wbr A F (Class.cv x))).fv) 0
  have support_mem_0000 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0001 : alpha_dummy_010 ∈ (((Class.cv alpha_dummy_010)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0002 :
    alpha_dummy_015 ∈
      (((Wff.classMem (Class.cv alpha_dummy_015) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_015) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_015)).fv) :=
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
    alpha_dummy_017 ∈
      (((Wff.classMem (Class.cv alpha_dummy_017) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_017) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_017)).fv) :=
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
    alpha_dummy_015 ∈ (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0005 :
    alpha_dummy_017 ∈ (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0006 :
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
  have support_mem_0007 :
    alpha_dummy_025 ∈
      (((syn_cnin (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0008 :
    alpha_dummy_022 ∈
      (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0009 :
    alpha_dummy_025 ∈
      (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_026)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0010 :
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
  have support_mem_0011 :
    alpha_dummy_026 ∈
      (((syn_cnin (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cnin]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0012 :
    alpha_dummy_023 ∈
      (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0013 :
    alpha_dummy_026 ∈
      (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_026)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0014 :
    alpha_dummy_022 ∈
      (((syn_ccompl (Class.cv alpha_dummy_022))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0015 :
    alpha_dummy_025 ∈
      (((syn_ccompl (Class.cv alpha_dummy_025))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_026))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0016 :
    alpha_dummy_022 ∈
      (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0017 :
    alpha_dummy_025 ∈
      (((Class.cv alpha_dummy_025)).fv ∪ ((Class.cv alpha_dummy_025)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0018 :
    alpha_dummy_023 ∈
      (((syn_ccompl (Class.cv alpha_dummy_022))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_023))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0019 :
    alpha_dummy_026 ∈
      (((syn_ccompl (Class.cv alpha_dummy_025))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_026))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0020 :
    alpha_dummy_023 ∈
      (((Class.cv alpha_dummy_023)).fv ∪ ((Class.cv alpha_dummy_023)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0021 :
    alpha_dummy_026 ∈
      (((Class.cv alpha_dummy_026)).fv ∪ ((Class.cv alpha_dummy_026)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0022 : alpha_dummy_000 ∈ ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0023 :
    alpha_dummy_000 ∈
      (((syn_ccompl (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
                (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cphi (Class.cv alpha_dummy_008))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_008))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0024 : x ∈ ((A).fv ∪ ((Class.cv x)).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0025 :
    x ∈
      (((syn_ccompl (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
                (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cphi (Class.cv alpha_dummy_010))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
                (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_010))
                    (syn_csn (syn_c0c)))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccompl]
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0026 :
    alpha_dummy_000 ∈
      (((Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_007)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_008)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_007)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_008)) (syn_csn (syn_c0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0027 :
    x ∈
      (((Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_009)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_010)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
              (Wff.classEq (Class.cv alpha_dummy_009)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_010)) (syn_csn (syn_c0c))))))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
    · rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 1))
      · rw [fv_class_cv]
        exact Finset.mem_singleton_self _
  have support_mem_0028 :
    alpha_dummy_008 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_008)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0029 :
    alpha_dummy_010 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_010)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_ccompl]
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0030 :
    alpha_dummy_008 ∈
      (((syn_cphi (Class.cv alpha_dummy_008))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_008))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0031 :
    alpha_dummy_010 ∈
      (((syn_cphi (Class.cv alpha_dummy_010))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_010))).fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_cphi]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0032 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have support_mem_0033 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) :=
    by
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _
  have focused_notmem_0000 : alpha_dummy_000 ∉ A.fv :=
    by
    change freshVar ((F).fv ∪ (A).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (hu))
  have focused_notmem_0001 : alpha_dummy_001 ∉ A.fv :=
    by
    change
      freshVar
          (({ alpha_dummy_000 } : Finset Var) ∪ ((syn_wbr A F (Class.cv alpha_dummy_000))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wbr A F (Class.cv alpha_dummy_000)).symm ▸
              (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))))
  have focused_notmem_0002 : alpha_dummy_003 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_001 (Wff.classEq
                (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                (syn_csn (Class.cv alpha_dummy_001))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => ((fv_class_cab alpha_dummy_001 (Wff.classEq
                  (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                  (syn_csn (Class.cv alpha_dummy_001)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0001) (h_eq ▸ hu)), (((fv_wff_classEq
                      (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                      (syn_csn (Class.cv alpha_dummy_001))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab alpha_dummy_000
                          (syn_wbr A F (Class.cv alpha_dummy_000))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0000) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv alpha_dummy_000)).symm ▸
                            (Finset.mem_union_left _
                              (Finset.mem_union_left _ (hu)))))⟩))))))⟩)))
  have wpp_notmem_0000 : alpha_dummy_003 ∉ (A).fv := by exact focused_notmem_0002
  have focused_notmem_0003 : alpha_dummy_002 ∉ A.fv :=
    by
    change freshVar (({ x } : Finset Var) ∪ ((syn_wbr A F (Class.cv x))).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _ (((fv_syn_wbr A F (Class.cv x)).symm ▸
              (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))))
  have focused_notmem_0004 : alpha_dummy_005 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                (syn_csn (Class.cv alpha_dummy_002))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => ((fv_class_cab alpha_dummy_002
                (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                  (syn_csn (Class.cv alpha_dummy_002)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0003) (h_eq ▸ hu)),
                (((fv_wff_classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                      (syn_csn (Class.cv alpha_dummy_002))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab x (syn_wbr A F (Class.cv x))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv x)).symm ▸ (Finset.mem_union_left _
                              (Finset.mem_union_left _ (hu)))))⟩))))))⟩)))
  have wpp_notmem_0001 : alpha_dummy_005 ∉ (A).fv := by exact focused_notmem_0004
  have focused_notmem_0005 : alpha_dummy_004 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_001 (Wff.classEq
                (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                (syn_csn (Class.cv alpha_dummy_001))))).fv)
          1 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => ((fv_class_cab alpha_dummy_001 (Wff.classEq
                  (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                  (syn_csn (Class.cv alpha_dummy_001)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0001) (h_eq ▸ hu)), (((fv_wff_classEq
                      (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                      (syn_csn (Class.cv alpha_dummy_001))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab alpha_dummy_000
                          (syn_wbr A F (Class.cv alpha_dummy_000))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0000) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv alpha_dummy_000)).symm ▸
                            (Finset.mem_union_left _
                              (Finset.mem_union_left _ (hu)))))⟩))))))⟩)))
  have wpp_notmem_0002 : alpha_dummy_004 ∉ (A).fv := by exact focused_notmem_0005
  have focused_notmem_0006 : alpha_dummy_006 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                (syn_csn (Class.cv alpha_dummy_002))))).fv)
          1 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => ((fv_class_cab alpha_dummy_002
                (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                  (syn_csn (Class.cv alpha_dummy_002)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0003) (h_eq ▸ hu)),
                (((fv_wff_classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                      (syn_csn (Class.cv alpha_dummy_002))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab x (syn_wbr A F (Class.cv x))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv x)).symm ▸ (Finset.mem_union_left _
                              (Finset.mem_union_left _ (hu)))))⟩))))))⟩)))
  have wpp_notmem_0003 : alpha_dummy_006 ∉ (A).fv := by exact focused_notmem_0006
  have wpp_notmem_0004 : alpha_dummy_001 ∉ (A).fv := by exact focused_notmem_0001
  have wpp_notmem_0005 : alpha_dummy_002 ∉ (A).fv := by exact focused_notmem_0003
  have wpp_notmem_0006 : alpha_dummy_000 ∉ (A).fv := by exact focused_notmem_0000
  have wpp_notmem_0007 : x ∉ (A).fv := by exact dv_A_x
  have focused_notmem_0007 : alpha_dummy_008 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0008 : alpha_dummy_007 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0009 : alpha_dummy_011 ∉ A.fv :=
    by
    change
      freshVar
          (((syn_ccompl (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
                    (Wff.classEq (Class.cv alpha_dummy_007)
                      (syn_cphi (Class.cv alpha_dummy_008))))))).fv ∪ ((syn_ccompl
                (Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
                    (Wff.classEq (Class.cv alpha_dummy_007)
                      (syn_cun (syn_cphi (Class.cv alpha_dummy_008))
                        (syn_csn (syn_c0c)))))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_syn_ccompl (Class.cab alpha_dummy_007
                    (syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                        (syn_cphi (Class.cv alpha_dummy_008)))))).symm ▸
              (((fv_class_cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
                      (Wff.classEq (Class.cv alpha_dummy_007)
                        (syn_cphi (Class.cv alpha_dummy_008))))).symm ▸ (Finset.mem_erase.mpr
                  ⟨(fun h_eq => (focused_notmem_0008) (h_eq ▸ hu)),
                    (((fv_syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                            (syn_cphi (Class.cv alpha_dummy_008)))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (focused_notmem_0007) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0008 : alpha_dummy_011 ∉ (A).fv := by exact focused_notmem_0009
  have focused_notmem_0010 : alpha_dummy_010 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ ((Class.cv x)).fv) 1 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0011 : alpha_dummy_009 ∉ A.fv :=
    by
    change freshVar ((A).fv ∪ ((Class.cv x)).fv) 0 ∉ A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0012 : alpha_dummy_012 ∉ A.fv :=
    by
    change
      freshVar
          (((syn_ccompl (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
                    (Wff.classEq (Class.cv alpha_dummy_009)
                      (syn_cphi (Class.cv alpha_dummy_010))))))).fv ∪ ((syn_ccompl
                (Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 (Class.cv x)
                    (Wff.classEq (Class.cv alpha_dummy_009)
                      (syn_cun (syn_cphi (Class.cv alpha_dummy_010))
                        (syn_csn (syn_c0c)))))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_syn_ccompl (Class.cab alpha_dummy_009
                    (syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                        (syn_cphi (Class.cv alpha_dummy_010)))))).symm ▸
              (((fv_class_cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
                      (Wff.classEq (Class.cv alpha_dummy_009)
                        (syn_cphi (Class.cv alpha_dummy_010))))).symm ▸ (Finset.mem_erase.mpr
                  ⟨(fun h_eq => (focused_notmem_0011) (h_eq ▸ hu)),
                    (((fv_syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                            (syn_cphi (Class.cv alpha_dummy_010)))).symm ▸
                      (Finset.mem_union_left _ (Finset.mem_erase.mpr
                          ⟨(fun h_eq => (focused_notmem_0010) (h_eq ▸ hu)), (hu)⟩))))⟩))))))
  have wpp_notmem_0009 : alpha_dummy_012 ∉ (A).fv := by exact focused_notmem_0012
  have focused_notmem_0013 : alpha_dummy_013 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_007 (syn_wrex alpha_dummy_008 A
                  (Wff.classEq (Class.cv alpha_dummy_007)
                    (syn_cphi (Class.cv alpha_dummy_008)))))).fv ∪ ((Class.cab alpha_dummy_007
                (syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                    (syn_cphi (Class.cv alpha_dummy_008)))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab alpha_dummy_007
                  (syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                      (syn_cphi (Class.cv alpha_dummy_008))))).symm ▸ (Finset.mem_erase.mpr
                ⟨(fun h_eq => (focused_notmem_0008) (h_eq ▸ hu)),
                  (((fv_syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                          (syn_cphi (Class.cv alpha_dummy_008)))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0007) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0010 : alpha_dummy_013 ∉ (A).fv := by exact focused_notmem_0013
  have focused_notmem_0014 : alpha_dummy_014 ∉ A.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_009 (syn_wrex alpha_dummy_010 A
                  (Wff.classEq (Class.cv alpha_dummy_009)
                    (syn_cphi (Class.cv alpha_dummy_010)))))).fv ∪ ((Class.cab alpha_dummy_009
                (syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                    (syn_cphi (Class.cv alpha_dummy_010)))))).fv)
          0 ∉
        A.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (((fv_class_cab alpha_dummy_009
                  (syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                      (syn_cphi (Class.cv alpha_dummy_010))))).symm ▸ (Finset.mem_erase.mpr
                ⟨(fun h_eq => (focused_notmem_0011) (h_eq ▸ hu)),
                  (((fv_syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                          (syn_cphi (Class.cv alpha_dummy_010)))).symm ▸
                    (Finset.mem_union_left _ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0010) (h_eq ▸ hu)), (hu)⟩))))⟩))))
  have wpp_notmem_0011 : alpha_dummy_014 ∉ (A).fv := by exact focused_notmem_0014
  have wpp_notmem_0012 : alpha_dummy_007 ∉ (A).fv := by exact focused_notmem_0008
  have wpp_notmem_0013 : alpha_dummy_009 ∉ (A).fv := by exact focused_notmem_0011
  have wpp_notmem_0014 : alpha_dummy_008 ∉ (A).fv := by exact focused_notmem_0007
  have wpp_notmem_0015 : alpha_dummy_010 ∉ (A).fv := by exact focused_notmem_0010
  have wpp_refl_0000 :
    TReflOn
      [(alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (A).fv :=
    by
    intro u hu
    exact
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
                      (TAlphaVar.free (by simp) (by simp))))))))))
  have wpp_notmem_0016 : alpha_dummy_003 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0017 : alpha_dummy_005 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0018 : alpha_dummy_004 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0019 : alpha_dummy_006 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0020 : alpha_dummy_001 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0021 : alpha_dummy_002 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0022 : alpha_dummy_000 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0023 : x ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0024 : alpha_dummy_011 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0025 : alpha_dummy_012 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0026 : alpha_dummy_013 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0027 : alpha_dummy_014 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0028 : alpha_dummy_007 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0029 : alpha_dummy_009 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0030 : alpha_dummy_008 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0031 : alpha_dummy_010 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0032 : alpha_dummy_016 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0033 : alpha_dummy_018 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0034 : alpha_dummy_015 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0035 : alpha_dummy_017 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0036 : alpha_dummy_019 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0037 : alpha_dummy_020 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0038 : alpha_dummy_021 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0039 : alpha_dummy_024 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0040 : alpha_dummy_022 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0041 : alpha_dummy_025 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0042 : alpha_dummy_023 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0043 : alpha_dummy_026 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0001 :
    TReflOn
      [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
        (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
        (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
        (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      ((syn_c1c)).fv :=
    by
    intro u hu
    exact
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
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu))
                                  (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have wpp_notmem_0044 : alpha_dummy_003 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0045 : alpha_dummy_005 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0046 : alpha_dummy_004 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0047 : alpha_dummy_006 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0048 : alpha_dummy_001 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0049 : alpha_dummy_002 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0050 : alpha_dummy_000 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0051 : x ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0052 : alpha_dummy_011 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0053 : alpha_dummy_012 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0054 : alpha_dummy_013 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0055 : alpha_dummy_014 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0056 : alpha_dummy_007 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0057 : alpha_dummy_009 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0058 : alpha_dummy_008 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0059 : alpha_dummy_010 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0060 : alpha_dummy_016 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0061 : alpha_dummy_018 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0062 : alpha_dummy_015 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0063 : alpha_dummy_017 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0064 : alpha_dummy_019 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0065 : alpha_dummy_020 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0066 : alpha_dummy_021 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0067 : alpha_dummy_024 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0068 : alpha_dummy_022 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0069 : alpha_dummy_025 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0070 : alpha_dummy_023 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0071 : alpha_dummy_026 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0002 :
    TReflOn
      [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
        (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
        (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
        (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      ((syn_c0)).fv :=
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
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
                                  (TAlphaVar.free (by simp) (by simp))))))))))))))))
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
        (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
        (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
        (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_021)
            (syn_cun (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_024)
            (syn_cun (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))))) :=
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
                                  (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
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
                                  (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
            (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
            (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
            (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
            (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012),
            (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
            (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
          (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
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
                                    (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
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
  have wpp_notmem_0072 : alpha_dummy_003 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0073 : alpha_dummy_005 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0074 : alpha_dummy_004 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0075 : alpha_dummy_006 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0076 : alpha_dummy_001 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0077 : alpha_dummy_002 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0078 : alpha_dummy_000 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0079 : x ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0080 : alpha_dummy_011 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0081 : alpha_dummy_012 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0082 : alpha_dummy_013 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0083 : alpha_dummy_014 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0084 : alpha_dummy_007 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0085 : alpha_dummy_009 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0086 : alpha_dummy_008 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0087 : alpha_dummy_010 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0088 : alpha_dummy_016 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0089 : alpha_dummy_018 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0090 : alpha_dummy_015 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0091 : alpha_dummy_017 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0092 : alpha_dummy_019 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0093 : alpha_dummy_020 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0003 :
    TReflOn
      [(alpha_dummy_019, alpha_dummy_020), (alpha_dummy_015, alpha_dummy_017),
        (alpha_dummy_016, alpha_dummy_018), (alpha_dummy_008, alpha_dummy_010),
        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_013, alpha_dummy_014),
        (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
        (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_003, alpha_dummy_005)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0082) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0083) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu))
                            (TAlphaVar.free (by simp) (by simp)))))))))))))
  have split_alpha_0001 :
    TAlphaWff
      [(alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_008) A) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_007) (syn_cphi (Class.cv alpha_dummy_008)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_010) A) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_009) (syn_cphi (Class.cv alpha_dummy_010))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_reflOn
          [(alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
            (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012),
            (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
            (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
          A wpp_refl_0000)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide))
              (freshVar_injective ((A).fv ∪ ((Class.cv x)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                        (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there
                      (freshVar_injective (((Class.cv alpha_dummy_008)).fv) (by decide))
                      (freshVar_injective (((Class.cv alpha_dummy_010)).fv) (by decide))
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
        [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
        (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
        (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
        (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg split_alpha_0000)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                              [(alpha_dummy_019, alpha_dummy_020),
                                (alpha_dummy_015, alpha_dummy_017),
                                (alpha_dummy_016, alpha_dummy_018),
                                (alpha_dummy_008, alpha_dummy_010),
                                (alpha_dummy_007, alpha_dummy_009),
                                (alpha_dummy_013, alpha_dummy_014),
                                (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
                                (alpha_dummy_001, alpha_dummy_002),
                                (alpha_dummy_004, alpha_dummy_006),
                                (alpha_dummy_003, alpha_dummy_005)]
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
                              [(alpha_dummy_019, alpha_dummy_020),
                                (alpha_dummy_015, alpha_dummy_017),
                                (alpha_dummy_016, alpha_dummy_018),
                                (alpha_dummy_008, alpha_dummy_010),
                                (alpha_dummy_007, alpha_dummy_009),
                                (alpha_dummy_013, alpha_dummy_014),
                                (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
                                (alpha_dummy_001, alpha_dummy_002),
                                (alpha_dummy_004, alpha_dummy_006),
                                (alpha_dummy_003, alpha_dummy_005)]
                              (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))
  have wpp_notmem_0094 : alpha_dummy_037 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0095 : alpha_dummy_038 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0096 : alpha_dummy_039 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0097 : alpha_dummy_040 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0098 : alpha_dummy_041 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_notmem_0099 : alpha_dummy_042 ∉ ((syn_c1c)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c1c) ▸ h_mem))
  have wpp_refl_0004 :
    TReflOn
      [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
        (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
        (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
        (alpha_dummy_041, alpha_dummy_042), (alpha_dummy_039, alpha_dummy_040),
        (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_037, alpha_dummy_038), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      ((syn_c1c)).fv :=
    by
    intro u hu
    exact
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0098) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0099) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0096) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0097) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0030) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0031) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0028) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0029) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0094) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0095) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0024) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0025) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0022) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0023) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0020) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0021) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0018) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0019) (h_eq ▸ hu)) (TAlphaVar.there
                                      (fun h_eq => (wpp_notmem_0016) (h_eq ▸ hu))
                                      (fun h_eq => (wpp_notmem_0017) (h_eq ▸ hu))
                                      (TAlphaVar.free (by simp) (by simp))))))))))))))))))
  have wpp_notmem_0100 : alpha_dummy_037 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0101 : alpha_dummy_038 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0102 : alpha_dummy_039 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0103 : alpha_dummy_040 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0104 : alpha_dummy_041 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_notmem_0105 : alpha_dummy_042 ∉ ((syn_c0)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0) ▸ h_mem))
  have wpp_refl_0005 :
    TReflOn
      [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
        (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
        (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
        (alpha_dummy_041, alpha_dummy_042), (alpha_dummy_039, alpha_dummy_040),
        (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_037, alpha_dummy_038), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      ((syn_c0)).fv :=
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
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0104) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0105) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0102) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0103) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0058) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0059) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0056) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0057) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0100) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0101) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0052) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0053) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0050) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0051) (h_eq ▸ hu)) (TAlphaVar.there
                                  (fun h_eq => (wpp_notmem_0048) (h_eq ▸ hu))
                                  (fun h_eq => (wpp_notmem_0049) (h_eq ▸ hu)) (TAlphaVar.there
                                    (fun h_eq => (wpp_notmem_0046) (h_eq ▸ hu))
                                    (fun h_eq => (wpp_notmem_0047) (h_eq ▸ hu)) (TAlphaVar.there
                                      (fun h_eq => (wpp_notmem_0044) (h_eq ▸ hu))
                                      (fun h_eq => (wpp_notmem_0045) (h_eq ▸ hu))
                                      (TAlphaVar.free (by simp) (by simp))))))))))))))))))
  have split_alpha_0002 :
    TAlphaWff
      [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
        (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
        (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
        (alpha_dummy_041, alpha_dummy_042), (alpha_dummy_039, alpha_dummy_040),
        (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_037, alpha_dummy_038), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_021)
            (syn_cun (Class.cv alpha_dummy_022) (Class.cv alpha_dummy_023)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_024)
            (syn_cun (Class.cv alpha_dummy_025) (Class.cv alpha_dummy_026))))) :=
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
                                  (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
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
                                  (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
          [(alpha_dummy_023, alpha_dummy_026), (alpha_dummy_022, alpha_dummy_025),
            (alpha_dummy_021, alpha_dummy_024), (alpha_dummy_019, alpha_dummy_020),
            (alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
            (alpha_dummy_041, alpha_dummy_042), (alpha_dummy_039, alpha_dummy_040),
            (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
            (alpha_dummy_037, alpha_dummy_038), (alpha_dummy_011, alpha_dummy_012),
            (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
            (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
          (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq
          (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
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
                                    (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_015)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_017)).fv ∪ ((syn_c1c)).fv)
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
  have wpp_notmem_0106 : alpha_dummy_037 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0107 : alpha_dummy_038 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0108 : alpha_dummy_039 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0109 : alpha_dummy_040 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0110 : alpha_dummy_041 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_notmem_0111 : alpha_dummy_042 ∉ ((syn_cnnc)).fv := by
    exact (fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_cnnc) ▸ h_mem))
  have wpp_refl_0006 :
    TReflOn
      [(alpha_dummy_019, alpha_dummy_020), (alpha_dummy_015, alpha_dummy_017),
        (alpha_dummy_016, alpha_dummy_018), (alpha_dummy_041, alpha_dummy_042),
        (alpha_dummy_039, alpha_dummy_040), (alpha_dummy_008, alpha_dummy_010),
        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_037, alpha_dummy_038),
        (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
        (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_003, alpha_dummy_005)]
      ((syn_cnnc)).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0092) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0093) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0090) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0091) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0088) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0089) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0110) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0111) (h_eq ▸ hu))
              (TAlphaVar.there (fun h_eq => (wpp_notmem_0108) (h_eq ▸ hu))
                (fun h_eq => (wpp_notmem_0109) (h_eq ▸ hu))
                (TAlphaVar.there (fun h_eq => (wpp_notmem_0086) (h_eq ▸ hu))
                  (fun h_eq => (wpp_notmem_0087) (h_eq ▸ hu))
                  (TAlphaVar.there (fun h_eq => (wpp_notmem_0084) (h_eq ▸ hu))
                    (fun h_eq => (wpp_notmem_0085) (h_eq ▸ hu))
                    (TAlphaVar.there (fun h_eq => (wpp_notmem_0106) (h_eq ▸ hu))
                      (fun h_eq => (wpp_notmem_0107) (h_eq ▸ hu))
                      (TAlphaVar.there (fun h_eq => (wpp_notmem_0080) (h_eq ▸ hu))
                        (fun h_eq => (wpp_notmem_0081) (h_eq ▸ hu))
                        (TAlphaVar.there (fun h_eq => (wpp_notmem_0078) (h_eq ▸ hu))
                          (fun h_eq => (wpp_notmem_0079) (h_eq ▸ hu))
                          (TAlphaVar.there (fun h_eq => (wpp_notmem_0076) (h_eq ▸ hu))
                            (fun h_eq => (wpp_notmem_0077) (h_eq ▸ hu))
                            (TAlphaVar.there (fun h_eq => (wpp_notmem_0074) (h_eq ▸ hu))
                              (fun h_eq => (wpp_notmem_0075) (h_eq ▸ hu))
                              (TAlphaVar.there (fun h_eq => (wpp_notmem_0072) (h_eq ▸ hu))
                                (fun h_eq => (wpp_notmem_0073) (h_eq ▸ hu))
                                (TAlphaVar.free (by simp) (by simp)))))))))))))))
  have split_alpha_0003 :
    TAlphaWff
      [(alpha_dummy_015, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_018),
        (alpha_dummy_041, alpha_dummy_042), (alpha_dummy_039, alpha_dummy_040),
        (alpha_dummy_008, alpha_dummy_010), (alpha_dummy_007, alpha_dummy_009),
        (alpha_dummy_037, alpha_dummy_038), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv alpha_dummy_015) (Class.cv alpha_dummy_008))
          (Wff.classEq (Class.cv alpha_dummy_016)
            (syn_cif (Wff.classMem (Class.cv alpha_dummy_015) (syn_cnnc))
              (syn_cplc (Class.cv alpha_dummy_015) (syn_c1c)) (Class.cv alpha_dummy_015)))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv alpha_dummy_017) (Class.cv alpha_dummy_010))
          (Wff.classEq (Class.cv alpha_dummy_018)
            (syn_cif (Wff.classMem (Class.cv alpha_dummy_017) (syn_cnnc))
              (syn_cplc (Class.cv alpha_dummy_017) (syn_c1c)) (Class.cv alpha_dummy_017))))) :=
    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_008)).fv) (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_010)).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed [(alpha_dummy_023, alpha_dummy_026),
                                    (alpha_dummy_022, alpha_dummy_025),
                                    (alpha_dummy_021, alpha_dummy_024),
                                    (alpha_dummy_019, alpha_dummy_020),
                                    (alpha_dummy_015, alpha_dummy_017),
                                    (alpha_dummy_016, alpha_dummy_018),
                                    (alpha_dummy_041, alpha_dummy_042),
                                    (alpha_dummy_039, alpha_dummy_040),
                                    (alpha_dummy_008, alpha_dummy_010),
                                    (alpha_dummy_007, alpha_dummy_009),
                                    (alpha_dummy_037, alpha_dummy_038),
                                    (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
                                    (alpha_dummy_001, alpha_dummy_002),
                                    (alpha_dummy_004, alpha_dummy_006),
                                    (alpha_dummy_003, alpha_dummy_005)]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg split_alpha_0002))))))) (TAlphaWff.classMem
                    (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [(alpha_dummy_019, alpha_dummy_020), (alpha_dummy_015, alpha_dummy_017),
                        (alpha_dummy_016, alpha_dummy_018), (alpha_dummy_041, alpha_dummy_042),
                        (alpha_dummy_039, alpha_dummy_040), (alpha_dummy_008, alpha_dummy_010),
                        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_037, alpha_dummy_038),
                        (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
                        (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_004, alpha_dummy_006),
                        (alpha_dummy_003, alpha_dummy_005)]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [(alpha_dummy_019, alpha_dummy_020), (alpha_dummy_015, alpha_dummy_017),
                        (alpha_dummy_016, alpha_dummy_018), (alpha_dummy_041, alpha_dummy_042),
                        (alpha_dummy_039, alpha_dummy_040), (alpha_dummy_008, alpha_dummy_010),
                        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_037, alpha_dummy_038),
                        (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
                        (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_004, alpha_dummy_006),
                        (alpha_dummy_003, alpha_dummy_005)]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))
  have wpp_notmem_0112 : alpha_dummy_003 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0113 : alpha_dummy_005 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0114 : alpha_dummy_004 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0115 : alpha_dummy_006 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0116 : alpha_dummy_001 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0117 : alpha_dummy_002 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0118 : alpha_dummy_000 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0119 : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0120 : alpha_dummy_011 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0121 : alpha_dummy_012 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0122 : alpha_dummy_037 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0123 : alpha_dummy_038 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0124 : alpha_dummy_007 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0125 : alpha_dummy_009 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0126 : alpha_dummy_008 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0127 : alpha_dummy_010 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0128 : alpha_dummy_039 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_notmem_0129 : alpha_dummy_040 ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
    exact
      (fun h_mem => ((fun h_mem =>
            ((fun h_mem => ((fun h_mem => (by simp at h_mem))) ((fv_syn_c0c) ▸ h_mem)))
              ((fv_syn_csn (syn_c0c)) ▸ h_mem))) ((fv_syn_ccompl (syn_csn (syn_c0c))) ▸ h_mem))
  have wpp_refl_0007 :
    TReflOn
      [(alpha_dummy_039, alpha_dummy_040), (alpha_dummy_008, alpha_dummy_010),
        (alpha_dummy_007, alpha_dummy_009), (alpha_dummy_037, alpha_dummy_038),
        (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
        (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_003, alpha_dummy_005)]
      ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0128) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0129) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0126) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0127) (h_eq ▸ hu))
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
                        (TAlphaVar.free (by simp) (by simp)))))))))))
  have split_alpha_0004 :
    TAlphaWff
      [(alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
        (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_011) (syn_ccompl (Class.cab alpha_dummy_007
              (syn_wrex alpha_dummy_008 A (Wff.classEq (Class.cv alpha_dummy_007)
                  (syn_cphi (Class.cv alpha_dummy_008))))))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_011) (syn_ccompl (Class.cab alpha_dummy_007
                (syn_wrex alpha_dummy_008 (Class.cv alpha_dummy_000)
                  (Wff.classEq (Class.cv alpha_dummy_007)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_008)) (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_012) (syn_ccompl (Class.cab alpha_dummy_009
              (syn_wrex alpha_dummy_010 A (Wff.classEq (Class.cv alpha_dummy_009)
                  (syn_cphi (Class.cv alpha_dummy_010))))))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_012) (syn_ccompl (Class.cab alpha_dummy_009
                (syn_wrex alpha_dummy_010 (Class.cv x) (Wff.classEq (Class.cv alpha_dummy_009)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_010))
                      (syn_csn (syn_c0c)))))))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg split_alpha_0001))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg split_alpha_0001))))))))
      (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 1))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide))
                              (freshVar_injective ((A).fv ∪ ((Class.cv x)).fv) (by decide))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.all split_alpha_0003)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.all split_alpha_0003)))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [(alpha_dummy_039, alpha_dummy_040),
                                      (alpha_dummy_008, alpha_dummy_010),
                                      (alpha_dummy_007, alpha_dummy_009),
                                      (alpha_dummy_037, alpha_dummy_038),
                                      (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
                                      (alpha_dummy_001, alpha_dummy_002),
                                      (alpha_dummy_004, alpha_dummy_006),
                                      (alpha_dummy_003, alpha_dummy_005)]
                                    (syn_ccompl (syn_csn (syn_c0c))) (by
                                      simp only [fv_syn_ccompl, fv_syn_csn,
                                        fv_syn_c0c])))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 1))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                ((A).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide))
                              (freshVar_injective ((A).fv ∪ ((Class.cv x)).fv) (by decide))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.all split_alpha_0003)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.all split_alpha_0003)))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [(alpha_dummy_039, alpha_dummy_040),
                                      (alpha_dummy_008, alpha_dummy_010),
                                      (alpha_dummy_007, alpha_dummy_009),
                                      (alpha_dummy_037, alpha_dummy_038),
                                      (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_000, x),
                                      (alpha_dummy_001, alpha_dummy_002),
                                      (alpha_dummy_004, alpha_dummy_006),
                                      (alpha_dummy_003, alpha_dummy_005)]
                                    (syn_ccompl (syn_csn (syn_c0c))) (by
                                      simp only [fv_syn_ccompl, fv_syn_csn,
                                        fv_syn_c0c])))))))))))))))))
  have focused_notmem_0015 : alpha_dummy_000 ∉ F.fv :=
    by
    change freshVar ((F).fv ∪ (A).fv) 0 ∉ F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_left _ (hu))
  have focused_notmem_0016 : alpha_dummy_001 ∉ F.fv :=
    by
    change
      freshVar
          (({ alpha_dummy_000 } : Finset Var) ∪ ((syn_wbr A F (Class.cv alpha_dummy_000))).fv)
          0 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wbr A F (Class.cv alpha_dummy_000)).symm ▸
              (Finset.mem_union_right _ (hu)))))
  have focused_notmem_0017 : alpha_dummy_003 ∉ F.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_001 (Wff.classEq
                (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                (syn_csn (Class.cv alpha_dummy_001))))).fv)
          0 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => ((fv_class_cab alpha_dummy_001 (Wff.classEq
                  (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                  (syn_csn (Class.cv alpha_dummy_001)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0016) (h_eq ▸ hu)), (((fv_wff_classEq
                      (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                      (syn_csn (Class.cv alpha_dummy_001))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab alpha_dummy_000
                          (syn_wbr A F (Class.cv alpha_dummy_000))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0015) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv alpha_dummy_000)).symm ▸
                            (Finset.mem_union_right _ (hu))))⟩))))))⟩)))
  have wpp_notmem_0130 : alpha_dummy_003 ∉ (F).fv := by exact focused_notmem_0017
  have focused_notmem_0018 : alpha_dummy_002 ∉ F.fv :=
    by
    change freshVar (({ x } : Finset Var) ∪ ((syn_wbr A F (Class.cv x))).fv) 0 ∉ F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => Finset.mem_union_right _
            (((fv_syn_wbr A F (Class.cv x)).symm ▸ (Finset.mem_union_right _ (hu)))))
  have focused_notmem_0019 : alpha_dummy_005 ∉ F.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                (syn_csn (Class.cv alpha_dummy_002))))).fv)
          0 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun u hu => ((fv_class_cab alpha_dummy_002
                (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                  (syn_csn (Class.cv alpha_dummy_002)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0018) (h_eq ▸ hu)),
                (((fv_wff_classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                      (syn_csn (Class.cv alpha_dummy_002))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab x (syn_wbr A F (Class.cv x))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_F_x) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv x)).symm ▸
                            (Finset.mem_union_right _ (hu))))⟩))))))⟩)))
  have wpp_notmem_0131 : alpha_dummy_005 ∉ (F).fv := by exact focused_notmem_0019
  have focused_notmem_0020 : alpha_dummy_004 ∉ F.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_001 (Wff.classEq
                (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                (syn_csn (Class.cv alpha_dummy_001))))).fv)
          1 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => ((fv_class_cab alpha_dummy_001 (Wff.classEq
                  (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                  (syn_csn (Class.cv alpha_dummy_001)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0016) (h_eq ▸ hu)), (((fv_wff_classEq
                      (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                      (syn_csn (Class.cv alpha_dummy_001))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab alpha_dummy_000
                          (syn_wbr A F (Class.cv alpha_dummy_000))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (focused_notmem_0015) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv alpha_dummy_000)).symm ▸
                            (Finset.mem_union_right _ (hu))))⟩))))))⟩)))
  have wpp_notmem_0132 : alpha_dummy_004 ∉ (F).fv := by exact focused_notmem_0020
  have focused_notmem_0021 : alpha_dummy_006 ∉ F.fv :=
    by
    change
      freshVar
          (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                (syn_csn (Class.cv alpha_dummy_002))))).fv)
          1 ∉
        F.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
        (fun u hu => ((fv_class_cab alpha_dummy_002
                (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                  (syn_csn (Class.cv alpha_dummy_002)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (focused_notmem_0018) (h_eq ▸ hu)),
                (((fv_wff_classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                      (syn_csn (Class.cv alpha_dummy_002))).symm ▸ (Finset.mem_union_left _
                    (((fv_class_cab x (syn_wbr A F (Class.cv x))).symm ▸ (Finset.mem_erase.mpr
                        ⟨(fun h_eq => (dv_F_x) (h_eq ▸ hu)),
                          (((fv_syn_wbr A F (Class.cv x)).symm ▸
                            (Finset.mem_union_right _ (hu))))⟩))))))⟩)))
  have wpp_notmem_0133 : alpha_dummy_006 ∉ (F).fv := by exact focused_notmem_0021
  have wpp_notmem_0134 : alpha_dummy_001 ∉ (F).fv := by exact focused_notmem_0016
  have wpp_notmem_0135 : alpha_dummy_002 ∉ (F).fv := by exact focused_notmem_0018
  have wpp_notmem_0136 : alpha_dummy_000 ∉ (F).fv := by exact focused_notmem_0015
  have wpp_notmem_0137 : x ∉ (F).fv := by exact dv_F_x
  have wpp_refl_0008 :
    TReflOn
      [(alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (F).fv :=
    by
    intro u hu
    exact
      (TAlphaVar.there (fun h_eq => (wpp_notmem_0136) (h_eq ▸ hu))
        (fun h_eq => (wpp_notmem_0137) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => (wpp_notmem_0134) (h_eq ▸ hu))
          (fun h_eq => (wpp_notmem_0135) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => (wpp_notmem_0132) (h_eq ▸ hu))
            (fun h_eq => (wpp_notmem_0133) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => (wpp_notmem_0130) (h_eq ▸ hu))
              (fun h_eq => (wpp_notmem_0131) (h_eq ▸ hu))
              (TAlphaVar.free (by simp) (by simp))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alpha_dummy_001 (Wff.classEq
                        (Class.cab alpha_dummy_000 (syn_wbr A F (Class.cv alpha_dummy_000)))
                        (syn_csn (Class.cv alpha_dummy_001))))).fv) (by decide))
                (freshVar_injective (((Class.cab alpha_dummy_002
                      (Wff.classEq (Class.cab x (syn_wbr A F (Class.cv x)))
                        (syn_csn (Class.cv alpha_dummy_002))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0004)))
                      (TAlphaClass.refl_of_reflOn
                        [(alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002),
                          (alpha_dummy_004, alpha_dummy_006),
                          (alpha_dummy_003, alpha_dummy_005)] F wpp_refl_0008)))
                  (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                          (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
