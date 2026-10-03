/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001048Leaf2ndReflected001. -/


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

/-! Shared variable, support, and alpha-certificate components. -/


namespace SecondProjectionAlpha

@[expose]
def alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
def alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
def alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
def alpha_dummy_003 : Var :=
  (freshVar (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
      ((syn_wex alpha_dummy_002 (Wff.classEq (Class.cv alpha_dummy_000)
            (syn_cop (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_001))))).fv) 0)

@[expose]
def alpha_dummy_004 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((syn_wex z (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv y))))).fv) 0)

@[expose]
def alpha_dummy_005 : Var :=
  (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 0)

@[expose]
def alpha_dummy_006 : Var :=
  (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 1)

@[expose]
def alpha_dummy_007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
def alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
def alpha_dummy_009 : Var :=
  (freshVar (((syn_ccompl (Class.cab alpha_dummy_005
            (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_005)
                (syn_cphi (Class.cv alpha_dummy_006))))))).fv ∪ ((syn_ccompl
          (Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_005)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_006)) (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_010 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_007 x y)
            (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                (syn_cphi (Class.cv (alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_011 : Var :=
  (freshVar (((Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_000)
            (Wff.classEq (Class.cv alpha_dummy_005)
              (syn_cphi (Class.cv alpha_dummy_006)))))).fv ∪ ((Class.cab alpha_dummy_005
          (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_000)
            (Wff.classEq (Class.cv alpha_dummy_005)
              (syn_cphi (Class.cv alpha_dummy_006)))))).fv) 0)

@[expose]
def alpha_dummy_012 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_007 x y))
              (syn_cphi (Class.cv (alpha_dummy_008 x y))))))).fv ∪
      ((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_007 x y))
              (syn_cphi (Class.cv (alpha_dummy_008 x y))))))).fv) 0)

@[expose]
def alpha_dummy_013 : Var :=
  (freshVar (((Class.cv alpha_dummy_006)).fv) 0)

@[expose]
def alpha_dummy_014 : Var :=
  (freshVar (((Class.cv alpha_dummy_006)).fv) 1)

@[expose]
def alpha_dummy_015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_008 x y))).fv) 0)

@[expose]
def alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_008 x y))).fv) 1)

@[expose]
def alpha_dummy_017 : Var :=
  (freshVar (((Wff.classMem (Class.cv alpha_dummy_013) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv alpha_dummy_013) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_013)).fv)
    0)

@[expose]
def alpha_dummy_018 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_015 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_015 x y)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_015 x y))).fv) 0)

@[expose]
def alpha_dummy_019 : Var :=
  (freshVar (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_020 : Var :=
  (freshVar (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_021 : Var :=
  (freshVar (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_035 : Var :=
  (freshVar (((Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_001)
            (Wff.classEq (Class.cv alpha_dummy_005)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_006)) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_001)
            (Wff.classEq (Class.cv alpha_dummy_005)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_006)) (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
def alpha_dummy_036 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alpha_dummy_007 x y))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_008 x y))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alpha_dummy_007 x y))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_008 x y))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_037 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_006)))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_038 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_008 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_039 : Var :=
  (freshVar (((syn_cphi (Class.cv alpha_dummy_006))).fv ∪
      ((syn_cphi (Class.cv alpha_dummy_006))).fv) 0)

@[expose]
def alpha_dummy_040 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_008 x y)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_008 x y)))).fv) 0)

@[expose]
def alpha_dummy_041 : Var :=
  (freshVar (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 0)

@[expose]
def alpha_dummy_042 : Var :=
  (freshVar (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 1)

@[expose]
def alpha_dummy_043 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
def alpha_dummy_044 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
def alpha_dummy_045 : Var :=
  (freshVar (((syn_ccompl (Class.cab alpha_dummy_041
            (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_002)
              (Wff.classEq (Class.cv alpha_dummy_041)
                (syn_cphi (Class.cv alpha_dummy_042))))))).fv ∪ ((syn_ccompl
          (Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_041)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_042)) (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_046 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_043 y z)
            (syn_wrex (alpha_dummy_044 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                (syn_cphi (Class.cv (alpha_dummy_044 y z)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 y z)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_047 : Var :=
  (freshVar (((Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_002)
            (Wff.classEq (Class.cv alpha_dummy_041)
              (syn_cphi (Class.cv alpha_dummy_042)))))).fv ∪ ((Class.cab alpha_dummy_041
          (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_002)
            (Wff.classEq (Class.cv alpha_dummy_041)
              (syn_cphi (Class.cv alpha_dummy_042)))))).fv) 0)

@[expose]
def alpha_dummy_048 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_043 y z))
              (syn_cphi (Class.cv (alpha_dummy_044 y z))))))).fv ∪
      ((Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_043 y z))
              (syn_cphi (Class.cv (alpha_dummy_044 y z))))))).fv) 0)

@[expose]
def alpha_dummy_049 : Var :=
  (freshVar (((Class.cv alpha_dummy_042)).fv) 0)

@[expose]
def alpha_dummy_050 : Var :=
  (freshVar (((Class.cv alpha_dummy_042)).fv) 1)

@[expose]
def alpha_dummy_051 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_044 y z))).fv) 0)

@[expose]
def alpha_dummy_052 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_044 y z))).fv) 1)

@[expose]
def alpha_dummy_053 : Var :=
  (freshVar (((Wff.classMem (Class.cv alpha_dummy_049) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv alpha_dummy_049) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_049)).fv)
    0)

@[expose]
def alpha_dummy_054 (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_051 y z)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_051 y z)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_051 y z))).fv) 0)

@[expose]
def alpha_dummy_055 : Var :=
  (freshVar (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_056 : Var :=
  (freshVar (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_057 : Var :=
  (freshVar (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_058 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_059 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_060 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_071 : Var :=
  (freshVar (((Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_001)
            (Wff.classEq (Class.cv alpha_dummy_041)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_042)) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_001)
            (Wff.classEq (Class.cv alpha_dummy_041)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_042)) (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
def alpha_dummy_072 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv y)
            (Wff.classEq (Class.cv (alpha_dummy_043 y z))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 y z))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv y)
            (Wff.classEq (Class.cv (alpha_dummy_043 y z))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 y z))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_073 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_042)))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_074 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_044 y z))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_075 : Var :=
  (freshVar (((syn_cphi (Class.cv alpha_dummy_042))).fv ∪
      ((syn_cphi (Class.cv alpha_dummy_042))).fv) 0)

@[expose]
def alpha_dummy_076 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_044 y z)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_044 y z)))).fv) 0)

theorem support_mem_0000 :
    alpha_dummy_000 ∈
      (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
        ((syn_wex alpha_dummy_002 (Wff.classEq (Class.cv alpha_dummy_000)
              (syn_cop (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_001))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem support_mem_0001 (x : Var) (y : Var) (z : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z
            (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv y))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem support_mem_0002 :
    alpha_dummy_001 ∈
      (({ alpha_dummy_000 } : Finset Var) ∪ ({ alpha_dummy_001 } : Finset Var) ∪
        ((syn_wex alpha_dummy_002 (Wff.classEq (Class.cv alpha_dummy_000)
              (syn_cop (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_001))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem support_mem_0003 (x : Var) (y : Var) (z : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z
            (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv y))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem support_mem_0004 :
    alpha_dummy_000 ∈
      (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0005 :
    alpha_dummy_000 ∈
      (((syn_ccompl (Class.cab alpha_dummy_005
              (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_005)
                  (syn_cphi (Class.cv alpha_dummy_006))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_005)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_006))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0006 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (alpha_dummy_007 x y)
              (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                  (syn_cphi (Class.cv (alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_008 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0008 :
    alpha_dummy_000 ∈
      (((Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_005)
                (syn_cphi (Class.cv alpha_dummy_006)))))).fv ∪ ((Class.cab alpha_dummy_005
            (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_005)
                (syn_cphi (Class.cv alpha_dummy_006)))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                (syn_cphi (Class.cv (alpha_dummy_008 x y))))))).fv ∪
        ((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                (syn_cphi (Class.cv (alpha_dummy_008 x y))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0010 : alpha_dummy_006 ∈ (((Class.cv alpha_dummy_006)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0011 (x : Var) (y : Var) :
    (alpha_dummy_008 x y) ∈ (((Class.cv (alpha_dummy_008 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0012 :
    alpha_dummy_013 ∈
      (((Wff.classMem (Class.cv alpha_dummy_013) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_013) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_013)).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0013 (x : Var) (y : Var) :
    (alpha_dummy_015 x y) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_015 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_015 x y)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_015 x y))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0014 :
    alpha_dummy_013 ∈ (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0015 (x : Var) (y : Var) :
    (alpha_dummy_015 x y) ∈ (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0016 :
    alpha_dummy_020 ∈
      (((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0017 (x : Var) (y : Var) :
    (alpha_dummy_023 x y) ∈
      (((syn_cnin (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0018 :
    alpha_dummy_020 ∈
      (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_021)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0019 (x : Var) (y : Var) :
    (alpha_dummy_023 x y) ∈
      (((Class.cv (alpha_dummy_023 x y))).fv ∪ ((Class.cv (alpha_dummy_024 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0020 :
    alpha_dummy_021 ∈
      (((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0021 (x : Var) (y : Var) :
    (alpha_dummy_024 x y) ∈
      (((syn_cnin (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0022 :
    alpha_dummy_021 ∈
      (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_021)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0023 (x : Var) (y : Var) :
    (alpha_dummy_024 x y) ∈
      (((Class.cv (alpha_dummy_023 x y))).fv ∪ ((Class.cv (alpha_dummy_024 x y))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0024 :
    alpha_dummy_020 ∈
      (((syn_ccompl (Class.cv alpha_dummy_020))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_021))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0025 (x : Var) (y : Var) :
    (alpha_dummy_023 x y) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_023 x y)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_024 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0026 :
    alpha_dummy_020 ∈
      (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_020)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0027 (x : Var) (y : Var) :
    (alpha_dummy_023 x y) ∈
      (((Class.cv (alpha_dummy_023 x y))).fv ∪ ((Class.cv (alpha_dummy_023 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0028 :
    alpha_dummy_021 ∈
      (((syn_ccompl (Class.cv alpha_dummy_020))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_021))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0029 (x : Var) (y : Var) :
    (alpha_dummy_024 x y) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_023 x y)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_024 x y)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0030 :
    alpha_dummy_021 ∈
      (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_021)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0031 (x : Var) (y : Var) :
    (alpha_dummy_024 x y) ∈
      (((Class.cv (alpha_dummy_024 x y))).fv ∪ ((Class.cv (alpha_dummy_024 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0032 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0033 :
    alpha_dummy_001 ∈
      (((syn_ccompl (Class.cab alpha_dummy_005
              (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_005)
                  (syn_cphi (Class.cv alpha_dummy_006))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_005)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_006))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0034 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0035 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (alpha_dummy_007 x y)
              (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                  (syn_cphi (Class.cv (alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_008 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0036 :
    alpha_dummy_001 ∈
      (((Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_005)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_006)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_005 (syn_wrex alpha_dummy_006 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_005)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_006)) (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0037 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_007 x y)
            (syn_wrex (alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0038 :
    alpha_dummy_006 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_006)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0039 (x : Var) (y : Var) :
    (alpha_dummy_008 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_008 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0040 :
    alpha_dummy_006 ∈
      (((syn_cphi (Class.cv alpha_dummy_006))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_006))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0041 (x : Var) (y : Var) :
    (alpha_dummy_008 x y) ∈
      (((syn_cphi (Class.cv (alpha_dummy_008 x y)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_008 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0042 :
    alpha_dummy_002 ∈
      (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0043 :
    alpha_dummy_002 ∈
      (((syn_ccompl (Class.cab alpha_dummy_041
              (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_002)
                (Wff.classEq (Class.cv alpha_dummy_041)
                  (syn_cphi (Class.cv alpha_dummy_042))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_041)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_042))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0044 (y : Var) (z : Var) :
    z ∈ (((Class.cv z)).fv ∪ ((Class.cv y)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0045 (y : Var) (z : Var) :
    z ∈
      (((syn_ccompl (Class.cab (alpha_dummy_043 y z)
              (syn_wrex (alpha_dummy_044 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                  (syn_cphi (Class.cv (alpha_dummy_044 y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv y)
                (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 y z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0046 :
    alpha_dummy_002 ∈
      (((Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_002)
              (Wff.classEq (Class.cv alpha_dummy_041)
                (syn_cphi (Class.cv alpha_dummy_042)))))).fv ∪ ((Class.cab alpha_dummy_041
            (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_002)
              (Wff.classEq (Class.cv alpha_dummy_041)
                (syn_cphi (Class.cv alpha_dummy_042)))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0047 (y : Var) (z : Var) :
    z ∈
      (((Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                (syn_cphi (Class.cv (alpha_dummy_044 y z))))))).fv ∪
        ((Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                (syn_cphi (Class.cv (alpha_dummy_044 y z))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 y z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0048 : alpha_dummy_042 ∈ (((Class.cv alpha_dummy_042)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0049 (y : Var) (z : Var) :
    (alpha_dummy_044 y z) ∈ (((Class.cv (alpha_dummy_044 y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0050 :
    alpha_dummy_049 ∈
      (((Wff.classMem (Class.cv alpha_dummy_049) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_049) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_049)).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0051 (y : Var) (z : Var) :
    (alpha_dummy_051 y z) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_051 y z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_051 y z)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_051 y z))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0052 :
    alpha_dummy_049 ∈ (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0053 (y : Var) (z : Var) :
    (alpha_dummy_051 y z) ∈ (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0054 :
    alpha_dummy_056 ∈
      (((syn_cnin (Class.cv alpha_dummy_056) (Class.cv alpha_dummy_057))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_056) (Class.cv alpha_dummy_057))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0055 (y : Var) (z : Var) :
    (alpha_dummy_059 y z) ∈
      (((syn_cnin (Class.cv (alpha_dummy_059 y z)) (Class.cv (alpha_dummy_060 y z)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_059 y z)) (Class.cv (alpha_dummy_060 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0056 :
    alpha_dummy_056 ∈
      (((Class.cv alpha_dummy_056)).fv ∪ ((Class.cv alpha_dummy_057)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0057 (y : Var) (z : Var) :
    (alpha_dummy_059 y z) ∈
      (((Class.cv (alpha_dummy_059 y z))).fv ∪ ((Class.cv (alpha_dummy_060 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0058 :
    alpha_dummy_057 ∈
      (((syn_cnin (Class.cv alpha_dummy_056) (Class.cv alpha_dummy_057))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_056) (Class.cv alpha_dummy_057))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0059 (y : Var) (z : Var) :
    (alpha_dummy_060 y z) ∈
      (((syn_cnin (Class.cv (alpha_dummy_059 y z)) (Class.cv (alpha_dummy_060 y z)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_059 y z)) (Class.cv (alpha_dummy_060 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0060 :
    alpha_dummy_057 ∈
      (((Class.cv alpha_dummy_056)).fv ∪ ((Class.cv alpha_dummy_057)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0061 (y : Var) (z : Var) :
    (alpha_dummy_060 y z) ∈
      (((Class.cv (alpha_dummy_059 y z))).fv ∪ ((Class.cv (alpha_dummy_060 y z))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0062 :
    alpha_dummy_056 ∈
      (((syn_ccompl (Class.cv alpha_dummy_056))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_057))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0063 (y : Var) (z : Var) :
    (alpha_dummy_059 y z) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_059 y z)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_060 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0064 :
    alpha_dummy_056 ∈
      (((Class.cv alpha_dummy_056)).fv ∪ ((Class.cv alpha_dummy_056)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0065 (y : Var) (z : Var) :
    (alpha_dummy_059 y z) ∈
      (((Class.cv (alpha_dummy_059 y z))).fv ∪ ((Class.cv (alpha_dummy_059 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0066 :
    alpha_dummy_057 ∈
      (((syn_ccompl (Class.cv alpha_dummy_056))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_057))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0067 (y : Var) (z : Var) :
    (alpha_dummy_060 y z) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_059 y z)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_060 y z)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0068 :
    alpha_dummy_057 ∈
      (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_057)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0069 (y : Var) (z : Var) :
    (alpha_dummy_060 y z) ∈
      (((Class.cv (alpha_dummy_060 y z))).fv ∪ ((Class.cv (alpha_dummy_060 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0070 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0071 :
    alpha_dummy_001 ∈
      (((syn_ccompl (Class.cab alpha_dummy_041
              (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_002)
                (Wff.classEq (Class.cv alpha_dummy_041)
                  (syn_cphi (Class.cv alpha_dummy_042))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_041)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_042))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0072 (y : Var) (z : Var) :
    y ∈ (((Class.cv z)).fv ∪ ((Class.cv y)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0073 (y : Var) (z : Var) :
    y ∈
      (((syn_ccompl (Class.cab (alpha_dummy_043 y z)
              (syn_wrex (alpha_dummy_044 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                  (syn_cphi (Class.cv (alpha_dummy_044 y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv y)
                (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0074 :
    alpha_dummy_001 ∈
      (((Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_041)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_042)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_041 (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_041)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_042)) (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0075 (y : Var) (z : Var) :
    y ∈
      (((Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 y z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_043 y z)
            (syn_wrex (alpha_dummy_044 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 y z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0076 :
    alpha_dummy_042 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_042)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0077 (y : Var) (z : Var) :
    (alpha_dummy_044 y z) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_044 y z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0078 :
    alpha_dummy_042 ∈
      (((syn_cphi (Class.cv alpha_dummy_042))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_042))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0079 (y : Var) (z : Var) :
    (alpha_dummy_044 y z) ∈
      (((syn_cphi (Class.cv (alpha_dummy_044 y z)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_044 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end SecondProjectionAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
