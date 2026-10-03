/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001041CoReflected001. -/


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


namespace CompositionAlpha

@[expose]
def alpha_dummy_000 (A : Class) (B : Class) : Var :=
  (freshVar ((A).fv ∪ (B).fv) 0)

@[expose]
def alpha_dummy_001 (A : Class) (B : Class) : Var :=
  (freshVar ((A).fv ∪ (B).fv) 1)

@[expose]
def alpha_dummy_002 (A : Class) (B : Class) : Var :=
  (freshVar ((A).fv ∪ (B).fv) 2)

@[expose]
def alpha_dummy_003 (A : Class) (B : Class) : Var :=
  (freshVar (({(alpha_dummy_000 A B)} : Finset Var) ∪ ({(alpha_dummy_001 A B)} : Finset Var) ∪
      ((syn_wex (alpha_dummy_002 A B) (syn_wa
            (syn_wbr (Class.cv (alpha_dummy_000 A B)) B (Class.cv (alpha_dummy_002 A B)))
            (syn_wbr (Class.cv (alpha_dummy_002 A B)) A (Class.cv (alpha_dummy_001 A B)))))).fv)
    0)

@[expose]
def alpha_dummy_004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z
          (syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
            (syn_wbr (Class.cv z) A (Class.cv y))))).fv) 0)

@[expose]
def alpha_dummy_005 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv) 0)

@[expose]
def alpha_dummy_006 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv) 1)

@[expose]
def alpha_dummy_007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
def alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
def alpha_dummy_009 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_005 A B)
            (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_000 A B))
              (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                (syn_cphi (Class.cv (alpha_dummy_006 A B)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_005 A B)
            (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_001 A B))
              (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_006 A B)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

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
def alpha_dummy_011 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_005 A B)
          (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_000 A B))
            (Wff.classEq (Class.cv (alpha_dummy_005 A B))
              (syn_cphi (Class.cv (alpha_dummy_006 A B))))))).fv ∪
      ((Class.cab (alpha_dummy_005 A B)
          (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_000 A B))
            (Wff.classEq (Class.cv (alpha_dummy_005 A B))
              (syn_cphi (Class.cv (alpha_dummy_006 A B))))))).fv) 0)

@[expose]
def alpha_dummy_012 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_007 x y))
              (syn_cphi (Class.cv (alpha_dummy_008 x y))))))).fv ∪
      ((Class.cab (alpha_dummy_007 x y) (syn_wrex (alpha_dummy_008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_007 x y))
              (syn_cphi (Class.cv (alpha_dummy_008 x y))))))).fv) 0)

@[expose]
def alpha_dummy_013 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_006 A B))).fv) 0)

@[expose]
def alpha_dummy_014 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_006 A B))).fv) 1)

@[expose]
def alpha_dummy_015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_008 x y))).fv) 0)

@[expose]
def alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_008 x y))).fv) 1)

@[expose]
def alpha_dummy_017 (A : Class) (B : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_013 A B)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_013 A B)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_013 A B))).fv) 0)

@[expose]
def alpha_dummy_018 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_015 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_015 x y)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_015 x y))).fv) 0)

@[expose]
def alpha_dummy_019 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_020 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_021 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv) 2)

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
def alpha_dummy_035 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_005 A B)
          (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_001 A B))
            (Wff.classEq (Class.cv (alpha_dummy_005 A B))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_006 A B))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_005 A B)
          (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_001 A B))
            (Wff.classEq (Class.cv (alpha_dummy_005 A B))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_006 A B))) (syn_csn (syn_c0c))))))).fv)
    0)

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
def alpha_dummy_037 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_006 A B))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_038 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_008 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_039 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_006 A B)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_006 A B)))).fv) 0)

@[expose]
def alpha_dummy_040 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_008 x y)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_008 x y)))).fv) 0)

@[expose]
def alpha_dummy_041 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_002 A B))).fv) 0)

@[expose]
def alpha_dummy_042 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_002 A B))).fv) 1)

@[expose]
def alpha_dummy_043 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 0)

@[expose]
def alpha_dummy_044 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 1)

@[expose]
def alpha_dummy_045 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_041 A B)
            (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_000 A B))
              (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                (syn_cphi (Class.cv (alpha_dummy_042 A B)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_041 A B)
            (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_002 A B))
              (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_042 A B)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_046 (x : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_043 x z)
            (syn_wrex (alpha_dummy_044 x z) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                (syn_cphi (Class.cv (alpha_dummy_044 x z)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 x z)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_047 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_041 A B)
          (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_000 A B))
            (Wff.classEq (Class.cv (alpha_dummy_041 A B))
              (syn_cphi (Class.cv (alpha_dummy_042 A B))))))).fv ∪
      ((Class.cab (alpha_dummy_041 A B)
          (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_000 A B))
            (Wff.classEq (Class.cv (alpha_dummy_041 A B))
              (syn_cphi (Class.cv (alpha_dummy_042 A B))))))).fv) 0)

@[expose]
def alpha_dummy_048 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_043 x z))
              (syn_cphi (Class.cv (alpha_dummy_044 x z))))))).fv ∪
      ((Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_043 x z))
              (syn_cphi (Class.cv (alpha_dummy_044 x z))))))).fv) 0)

@[expose]
def alpha_dummy_049 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_042 A B))).fv) 0)

@[expose]
def alpha_dummy_050 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_042 A B))).fv) 1)

@[expose]
def alpha_dummy_051 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_044 x z))).fv) 0)

@[expose]
def alpha_dummy_052 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_044 x z))).fv) 1)

@[expose]
def alpha_dummy_053 (A : Class) (B : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_049 A B)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_049 A B)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_049 A B))).fv) 0)

@[expose]
def alpha_dummy_054 (x : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_051 x z)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_051 x z)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_051 x z))).fv) 0)

@[expose]
def alpha_dummy_055 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_056 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_057 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_058 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_059 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_060 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_071 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_041 A B)
          (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_002 A B))
            (Wff.classEq (Class.cv (alpha_dummy_041 A B))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_042 A B))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_041 A B)
          (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_002 A B))
            (Wff.classEq (Class.cv (alpha_dummy_041 A B))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_042 A B))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_072 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_043 x z))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 x z))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_043 x z))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 x z))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_073 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_042 A B))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_074 (x : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_044 x z))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_075 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_042 A B)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_042 A B)))).fv) 0)

@[expose]
def alpha_dummy_076 (x : Var) (z : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_044 x z)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_044 x z)))).fv) 0)

@[expose]
def alpha_dummy_077 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_002 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv) 0)

@[expose]
def alpha_dummy_078 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_002 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv) 1)

@[expose]
def alpha_dummy_079 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
def alpha_dummy_080 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
def alpha_dummy_081 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_077 A B)
            (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_002 A B))
              (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                (syn_cphi (Class.cv (alpha_dummy_078 A B)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_077 A B)
            (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_001 A B))
              (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_078 A B)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_082 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_079 y z)
            (syn_wrex (alpha_dummy_080 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                (syn_cphi (Class.cv (alpha_dummy_080 y z)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_080 y z)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_083 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_077 A B)
          (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_002 A B))
            (Wff.classEq (Class.cv (alpha_dummy_077 A B))
              (syn_cphi (Class.cv (alpha_dummy_078 A B))))))).fv ∪
      ((Class.cab (alpha_dummy_077 A B)
          (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_002 A B))
            (Wff.classEq (Class.cv (alpha_dummy_077 A B))
              (syn_cphi (Class.cv (alpha_dummy_078 A B))))))).fv) 0)

@[expose]
def alpha_dummy_084 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_079 y z))
              (syn_cphi (Class.cv (alpha_dummy_080 y z))))))).fv ∪
      ((Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_079 y z))
              (syn_cphi (Class.cv (alpha_dummy_080 y z))))))).fv) 0)

@[expose]
def alpha_dummy_085 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_078 A B))).fv) 0)

@[expose]
def alpha_dummy_086 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_078 A B))).fv) 1)

@[expose]
def alpha_dummy_087 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_080 y z))).fv) 0)

@[expose]
def alpha_dummy_088 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_080 y z))).fv) 1)

@[expose]
def alpha_dummy_089 (A : Class) (B : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_085 A B)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_085 A B)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_085 A B))).fv) 0)

@[expose]
def alpha_dummy_090 (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_087 y z)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_087 y z)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_087 y z))).fv) 0)

@[expose]
def alpha_dummy_091 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_092 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_093 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_094 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_095 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_096 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_107 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_077 A B)
          (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_001 A B))
            (Wff.classEq (Class.cv (alpha_dummy_077 A B))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_078 A B))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_077 A B)
          (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_001 A B))
            (Wff.classEq (Class.cv (alpha_dummy_077 A B))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_078 A B))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_108 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv y)
            (Wff.classEq (Class.cv (alpha_dummy_079 y z))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_080 y z))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv y)
            (Wff.classEq (Class.cv (alpha_dummy_079 y z))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_080 y z))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_109 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_078 A B))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_110 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_080 y z))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_111 (A : Class) (B : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_078 A B)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_078 A B)))).fv) 0)

@[expose]
def alpha_dummy_112 (y : Var) (z : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_080 y z)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_080 y z)))).fv) 0)

theorem support_mem_0000 (A : Class) (B : Class) :
    (alpha_dummy_000 A B) ∈
      (({(alpha_dummy_000 A B)} : Finset Var) ∪ ({(alpha_dummy_001 A B)} : Finset Var) ∪
        ((syn_wex (alpha_dummy_002 A B) (syn_wa (syn_wbr (Class.cv (alpha_dummy_000 A B)) B
                (Class.cv (alpha_dummy_002 A B))) (syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                (Class.cv (alpha_dummy_001 A B)))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem support_mem_0001 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z
            (syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
              (syn_wbr (Class.cv z) A (Class.cv y))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem support_mem_0002 (A : Class) (B : Class) :
    (alpha_dummy_001 A B) ∈
      (({(alpha_dummy_000 A B)} : Finset Var) ∪ ({(alpha_dummy_001 A B)} : Finset Var) ∪
        ((syn_wex (alpha_dummy_002 A B) (syn_wa (syn_wbr (Class.cv (alpha_dummy_000 A B)) B
                (Class.cv (alpha_dummy_002 A B))) (syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                (Class.cv (alpha_dummy_001 A B)))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem support_mem_0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z
            (syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
              (syn_wbr (Class.cv z) A (Class.cv y))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem support_mem_0004 (A : Class) (B : Class) :
    (alpha_dummy_000 A B) ∈
      (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0005 (A : Class) (B : Class) :
    (alpha_dummy_000 A B) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_005 A B)
              (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_000 A B))
                (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                  (syn_cphi (Class.cv (alpha_dummy_006 A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_005 A B)
              (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_001 A B))
                (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_006 A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A B) 1))
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

theorem support_mem_0008 (A : Class) (B : Class) :
    (alpha_dummy_000 A B) ∈
      (((Class.cab (alpha_dummy_005 A B)
            (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_000 A B))
              (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                (syn_cphi (Class.cv (alpha_dummy_006 A B))))))).fv ∪
        ((Class.cab (alpha_dummy_005 A B)
            (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_000 A B))
              (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                (syn_cphi (Class.cv (alpha_dummy_006 A B))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A B) 1))
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

theorem support_mem_0010 (A : Class) (B : Class) :
    (alpha_dummy_006 A B) ∈ (((Class.cv (alpha_dummy_006 A B))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0011 (x : Var) (y : Var) :
    (alpha_dummy_008 x y) ∈ (((Class.cv (alpha_dummy_008 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0012 (A : Class) (B : Class) :
    (alpha_dummy_013 A B) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_013 A B)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_013 A B)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_013 A B))).fv) :=
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

theorem support_mem_0014 (A : Class) (B : Class) :
    (alpha_dummy_013 A B) ∈ (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv) :=
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

theorem support_mem_0016 (A : Class) (B : Class) :
    (alpha_dummy_020 A B) ∈
      (((syn_cnin (Class.cv (alpha_dummy_020 A B)) (Class.cv (alpha_dummy_021 A B)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_020 A B)) (Class.cv (alpha_dummy_021 A B)))).fv) :=
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

theorem support_mem_0018 (A : Class) (B : Class) :
    (alpha_dummy_020 A B) ∈
      (((Class.cv (alpha_dummy_020 A B))).fv ∪ ((Class.cv (alpha_dummy_021 A B))).fv) :=
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

theorem support_mem_0020 (A : Class) (B : Class) :
    (alpha_dummy_021 A B) ∈
      (((syn_cnin (Class.cv (alpha_dummy_020 A B)) (Class.cv (alpha_dummy_021 A B)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_020 A B)) (Class.cv (alpha_dummy_021 A B)))).fv) :=
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

theorem support_mem_0022 (A : Class) (B : Class) :
    (alpha_dummy_021 A B) ∈
      (((Class.cv (alpha_dummy_020 A B))).fv ∪ ((Class.cv (alpha_dummy_021 A B))).fv) :=
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

theorem support_mem_0024 (A : Class) (B : Class) :
    (alpha_dummy_020 A B) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_020 A B)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_021 A B)))).fv) :=
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

theorem support_mem_0026 (A : Class) (B : Class) :
    (alpha_dummy_020 A B) ∈
      (((Class.cv (alpha_dummy_020 A B))).fv ∪ ((Class.cv (alpha_dummy_020 A B))).fv) :=
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

theorem support_mem_0028 (A : Class) (B : Class) :
    (alpha_dummy_021 A B) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_020 A B)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_021 A B)))).fv) :=
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

theorem support_mem_0030 (A : Class) (B : Class) :
    (alpha_dummy_021 A B) ∈
      (((Class.cv (alpha_dummy_021 A B))).fv ∪ ((Class.cv (alpha_dummy_021 A B))).fv) :=
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

theorem support_mem_0032 (A : Class) (B : Class) :
    (alpha_dummy_001 A B) ∈
      (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0033 (A : Class) (B : Class) :
    (alpha_dummy_001 A B) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_005 A B)
              (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_000 A B))
                (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                  (syn_cphi (Class.cv (alpha_dummy_006 A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_005 A B)
              (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_001 A B))
                (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_006 A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A B) 1))
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

theorem support_mem_0036 (A : Class) (B : Class) :
    (alpha_dummy_001 A B) ∈
      (((Class.cab (alpha_dummy_005 A B)
            (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_001 A B))
              (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_006 A B)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_005 A B)
            (syn_wrex (alpha_dummy_006 A B) (Class.cv (alpha_dummy_001 A B))
              (Wff.classEq (Class.cv (alpha_dummy_005 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_006 A B)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A B) 1))
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

theorem support_mem_0038 (A : Class) (B : Class) :
    (alpha_dummy_006 A B) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_006 A B))))).fv ∪
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

theorem support_mem_0040 (A : Class) (B : Class) :
    (alpha_dummy_006 A B) ∈
      (((syn_cphi (Class.cv (alpha_dummy_006 A B)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_006 A B)))).fv) :=
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

theorem support_mem_0042 (A : Class) (B : Class) :
    (alpha_dummy_000 A B) ∈
      (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_002 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0043 (A : Class) (B : Class) :
    (alpha_dummy_000 A B) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_041 A B)
              (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_000 A B))
                (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                  (syn_cphi (Class.cv (alpha_dummy_042 A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_041 A B)
              (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_002 A B))
                (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_042 A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0042 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0042 A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0044 (x : Var) (z : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0045 (x : Var) (z : Var) :
    x ∈
      (((syn_ccompl (Class.cab (alpha_dummy_043 x z)
              (syn_wrex (alpha_dummy_044 x z) (Class.cv x)
                (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                  (syn_cphi (Class.cv (alpha_dummy_044 x z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 x z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 x z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0046 (A : Class) (B : Class) :
    (alpha_dummy_000 A B) ∈
      (((Class.cab (alpha_dummy_041 A B)
            (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_000 A B))
              (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                (syn_cphi (Class.cv (alpha_dummy_042 A B))))))).fv ∪
        ((Class.cab (alpha_dummy_041 A B)
            (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_000 A B))
              (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                (syn_cphi (Class.cv (alpha_dummy_042 A B))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0042 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0042 A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0047 (x : Var) (z : Var) :
    x ∈
      (((Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                (syn_cphi (Class.cv (alpha_dummy_044 x z))))))).fv ∪
        ((Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                (syn_cphi (Class.cv (alpha_dummy_044 x z))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 x z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0048 (A : Class) (B : Class) :
    (alpha_dummy_042 A B) ∈ (((Class.cv (alpha_dummy_042 A B))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0049 (x : Var) (z : Var) :
    (alpha_dummy_044 x z) ∈ (((Class.cv (alpha_dummy_044 x z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0050 (A : Class) (B : Class) :
    (alpha_dummy_049 A B) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_049 A B)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_049 A B)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_049 A B))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0051 (x : Var) (z : Var) :
    (alpha_dummy_051 x z) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_051 x z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_051 x z)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_051 x z))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0052 (A : Class) (B : Class) :
    (alpha_dummy_049 A B) ∈ (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0053 (x : Var) (z : Var) :
    (alpha_dummy_051 x z) ∈ (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0054 (A : Class) (B : Class) :
    (alpha_dummy_056 A B) ∈
      (((syn_cnin (Class.cv (alpha_dummy_056 A B)) (Class.cv (alpha_dummy_057 A B)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_056 A B)) (Class.cv (alpha_dummy_057 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0055 (x : Var) (z : Var) :
    (alpha_dummy_059 x z) ∈
      (((syn_cnin (Class.cv (alpha_dummy_059 x z)) (Class.cv (alpha_dummy_060 x z)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_059 x z)) (Class.cv (alpha_dummy_060 x z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0056 (A : Class) (B : Class) :
    (alpha_dummy_056 A B) ∈
      (((Class.cv (alpha_dummy_056 A B))).fv ∪ ((Class.cv (alpha_dummy_057 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0057 (x : Var) (z : Var) :
    (alpha_dummy_059 x z) ∈
      (((Class.cv (alpha_dummy_059 x z))).fv ∪ ((Class.cv (alpha_dummy_060 x z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0058 (A : Class) (B : Class) :
    (alpha_dummy_057 A B) ∈
      (((syn_cnin (Class.cv (alpha_dummy_056 A B)) (Class.cv (alpha_dummy_057 A B)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_056 A B)) (Class.cv (alpha_dummy_057 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0059 (x : Var) (z : Var) :
    (alpha_dummy_060 x z) ∈
      (((syn_cnin (Class.cv (alpha_dummy_059 x z)) (Class.cv (alpha_dummy_060 x z)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_059 x z)) (Class.cv (alpha_dummy_060 x z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0060 (A : Class) (B : Class) :
    (alpha_dummy_057 A B) ∈
      (((Class.cv (alpha_dummy_056 A B))).fv ∪ ((Class.cv (alpha_dummy_057 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0061 (x : Var) (z : Var) :
    (alpha_dummy_060 x z) ∈
      (((Class.cv (alpha_dummy_059 x z))).fv ∪ ((Class.cv (alpha_dummy_060 x z))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0062 (A : Class) (B : Class) :
    (alpha_dummy_056 A B) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_056 A B)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_057 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0063 (x : Var) (z : Var) :
    (alpha_dummy_059 x z) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_059 x z)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_060 x z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0064 (A : Class) (B : Class) :
    (alpha_dummy_056 A B) ∈
      (((Class.cv (alpha_dummy_056 A B))).fv ∪ ((Class.cv (alpha_dummy_056 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0065 (x : Var) (z : Var) :
    (alpha_dummy_059 x z) ∈
      (((Class.cv (alpha_dummy_059 x z))).fv ∪ ((Class.cv (alpha_dummy_059 x z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0066 (A : Class) (B : Class) :
    (alpha_dummy_057 A B) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_056 A B)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_057 A B)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0067 (x : Var) (z : Var) :
    (alpha_dummy_060 x z) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_059 x z)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_060 x z)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0068 (A : Class) (B : Class) :
    (alpha_dummy_057 A B) ∈
      (((Class.cv (alpha_dummy_057 A B))).fv ∪ ((Class.cv (alpha_dummy_057 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0069 (x : Var) (z : Var) :
    (alpha_dummy_060 x z) ∈
      (((Class.cv (alpha_dummy_060 x z))).fv ∪ ((Class.cv (alpha_dummy_060 x z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0070 (A : Class) (B : Class) :
    (alpha_dummy_002 A B) ∈
      (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_002 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0071 (A : Class) (B : Class) :
    (alpha_dummy_002 A B) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_041 A B)
              (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_000 A B))
                (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                  (syn_cphi (Class.cv (alpha_dummy_042 A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_041 A B)
              (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_002 A B))
                (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_042 A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0072 (x : Var) (z : Var) :
    z ∈ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0073 (x : Var) (z : Var) :
    z ∈
      (((syn_ccompl (Class.cab (alpha_dummy_043 x z)
              (syn_wrex (alpha_dummy_044 x z) (Class.cv x)
                (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                  (syn_cphi (Class.cv (alpha_dummy_044 x z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 x z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 x z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0074 (A : Class) (B : Class) :
    (alpha_dummy_002 A B) ∈
      (((Class.cab (alpha_dummy_041 A B)
            (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_002 A B))
              (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_042 A B)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_041 A B)
            (syn_wrex (alpha_dummy_042 A B) (Class.cv (alpha_dummy_002 A B))
              (Wff.classEq (Class.cv (alpha_dummy_041 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_042 A B)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0075 (x : Var) (z : Var) :
    z ∈
      (((Class.cab (alpha_dummy_043 x z) (syn_wrex (alpha_dummy_044 x z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 x z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_043 x z)
            (syn_wrex (alpha_dummy_044 x z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_043 x z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 x z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 x z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 x z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0076 (A : Class) (B : Class) :
    (alpha_dummy_042 A B) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_042 A B))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0077 (x : Var) (z : Var) :
    (alpha_dummy_044 x z) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_044 x z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0078 (A : Class) (B : Class) :
    (alpha_dummy_042 A B) ∈
      (((syn_cphi (Class.cv (alpha_dummy_042 A B)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_042 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0079 (x : Var) (z : Var) :
    (alpha_dummy_044 x z) ∈
      (((syn_cphi (Class.cv (alpha_dummy_044 x z)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_044 x z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0080 (A : Class) (B : Class) :
    (alpha_dummy_002 A B) ∈
      (((Class.cv (alpha_dummy_002 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0081 (A : Class) (B : Class) :
    (alpha_dummy_002 A B) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_077 A B)
              (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_002 A B))
                (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                  (syn_cphi (Class.cv (alpha_dummy_078 A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_077 A B)
              (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_001 A B))
                (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_078 A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0082 (y : Var) (z : Var) :
    z ∈ (((Class.cv z)).fv ∪ ((Class.cv y)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0083 (y : Var) (z : Var) :
    z ∈
      (((syn_ccompl (Class.cab (alpha_dummy_079 y z)
              (syn_wrex (alpha_dummy_080 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                  (syn_cphi (Class.cv (alpha_dummy_080 y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv y)
                (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_080 y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 y z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0084 (A : Class) (B : Class) :
    (alpha_dummy_002 A B) ∈
      (((Class.cab (alpha_dummy_077 A B)
            (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_002 A B))
              (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                (syn_cphi (Class.cv (alpha_dummy_078 A B))))))).fv ∪
        ((Class.cab (alpha_dummy_077 A B)
            (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_002 A B))
              (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                (syn_cphi (Class.cv (alpha_dummy_078 A B))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0085 (y : Var) (z : Var) :
    z ∈
      (((Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                (syn_cphi (Class.cv (alpha_dummy_080 y z))))))).fv ∪
        ((Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                (syn_cphi (Class.cv (alpha_dummy_080 y z))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 y z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0086 (A : Class) (B : Class) :
    (alpha_dummy_078 A B) ∈ (((Class.cv (alpha_dummy_078 A B))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0087 (y : Var) (z : Var) :
    (alpha_dummy_080 y z) ∈ (((Class.cv (alpha_dummy_080 y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0088 (A : Class) (B : Class) :
    (alpha_dummy_085 A B) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_085 A B)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_085 A B)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_085 A B))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0089 (y : Var) (z : Var) :
    (alpha_dummy_087 y z) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_087 y z)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_087 y z)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_087 y z))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0090 (A : Class) (B : Class) :
    (alpha_dummy_085 A B) ∈ (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0091 (y : Var) (z : Var) :
    (alpha_dummy_087 y z) ∈ (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0092 (A : Class) (B : Class) :
    (alpha_dummy_092 A B) ∈
      (((syn_cnin (Class.cv (alpha_dummy_092 A B)) (Class.cv (alpha_dummy_093 A B)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_092 A B)) (Class.cv (alpha_dummy_093 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0093 (y : Var) (z : Var) :
    (alpha_dummy_095 y z) ∈
      (((syn_cnin (Class.cv (alpha_dummy_095 y z)) (Class.cv (alpha_dummy_096 y z)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_095 y z)) (Class.cv (alpha_dummy_096 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0094 (A : Class) (B : Class) :
    (alpha_dummy_092 A B) ∈
      (((Class.cv (alpha_dummy_092 A B))).fv ∪ ((Class.cv (alpha_dummy_093 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0095 (y : Var) (z : Var) :
    (alpha_dummy_095 y z) ∈
      (((Class.cv (alpha_dummy_095 y z))).fv ∪ ((Class.cv (alpha_dummy_096 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0096 (A : Class) (B : Class) :
    (alpha_dummy_093 A B) ∈
      (((syn_cnin (Class.cv (alpha_dummy_092 A B)) (Class.cv (alpha_dummy_093 A B)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_092 A B)) (Class.cv (alpha_dummy_093 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0097 (y : Var) (z : Var) :
    (alpha_dummy_096 y z) ∈
      (((syn_cnin (Class.cv (alpha_dummy_095 y z)) (Class.cv (alpha_dummy_096 y z)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_095 y z)) (Class.cv (alpha_dummy_096 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0098 (A : Class) (B : Class) :
    (alpha_dummy_093 A B) ∈
      (((Class.cv (alpha_dummy_092 A B))).fv ∪ ((Class.cv (alpha_dummy_093 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0099 (y : Var) (z : Var) :
    (alpha_dummy_096 y z) ∈
      (((Class.cv (alpha_dummy_095 y z))).fv ∪ ((Class.cv (alpha_dummy_096 y z))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0100 (A : Class) (B : Class) :
    (alpha_dummy_092 A B) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_092 A B)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_093 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0101 (y : Var) (z : Var) :
    (alpha_dummy_095 y z) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_095 y z)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_096 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0102 (A : Class) (B : Class) :
    (alpha_dummy_092 A B) ∈
      (((Class.cv (alpha_dummy_092 A B))).fv ∪ ((Class.cv (alpha_dummy_092 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0103 (y : Var) (z : Var) :
    (alpha_dummy_095 y z) ∈
      (((Class.cv (alpha_dummy_095 y z))).fv ∪ ((Class.cv (alpha_dummy_095 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0104 (A : Class) (B : Class) :
    (alpha_dummy_093 A B) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_092 A B)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_093 A B)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0105 (y : Var) (z : Var) :
    (alpha_dummy_096 y z) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_095 y z)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_096 y z)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0106 (A : Class) (B : Class) :
    (alpha_dummy_093 A B) ∈
      (((Class.cv (alpha_dummy_093 A B))).fv ∪ ((Class.cv (alpha_dummy_093 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0107 (y : Var) (z : Var) :
    (alpha_dummy_096 y z) ∈
      (((Class.cv (alpha_dummy_096 y z))).fv ∪ ((Class.cv (alpha_dummy_096 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0108 (A : Class) (B : Class) :
    (alpha_dummy_001 A B) ∈
      (((Class.cv (alpha_dummy_002 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0109 (A : Class) (B : Class) :
    (alpha_dummy_001 A B) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_077 A B)
              (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_002 A B))
                (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                  (syn_cphi (Class.cv (alpha_dummy_078 A B)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_077 A B)
              (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_001 A B))
                (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_078 A B)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0110 (y : Var) (z : Var) :
    y ∈ (((Class.cv z)).fv ∪ ((Class.cv y)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0111 (y : Var) (z : Var) :
    y ∈
      (((syn_ccompl (Class.cab (alpha_dummy_079 y z)
              (syn_wrex (alpha_dummy_080 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                  (syn_cphi (Class.cv (alpha_dummy_080 y z)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv y)
                (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_080 y z)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0112 (A : Class) (B : Class) :
    (alpha_dummy_001 A B) ∈
      (((Class.cab (alpha_dummy_077 A B)
            (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_001 A B))
              (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_078 A B)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_077 A B)
            (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_001 A B))
              (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_078 A B)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0113 (y : Var) (z : Var) :
    y ∈
      (((Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_080 y z)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_079 y z)
            (syn_wrex (alpha_dummy_080 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_080 y z)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0114 (A : Class) (B : Class) :
    (alpha_dummy_078 A B) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_078 A B))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0115 (y : Var) (z : Var) :
    (alpha_dummy_080 y z) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_080 y z))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0116 (A : Class) (B : Class) :
    (alpha_dummy_078 A B) ∈
      (((syn_cphi (Class.cv (alpha_dummy_078 A B)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_078 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0117 (y : Var) (z : Var) :
    (alpha_dummy_080 y z) ∈
      (((syn_cphi (Class.cv (alpha_dummy_080 y z)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_080 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem focused_notmem_0000 (A : Class) (B : Class) : (alpha_dummy_002 A B) ∉ B.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 2 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_right _ (hu))

theorem focused_notmem_0001 (A : Class) (B : Class) : (alpha_dummy_003 A B) ∉ B.fv :=
  by
  change
    freshVar
        (({(alpha_dummy_000 A B)} : Finset Var) ∪ ({(alpha_dummy_001 A B)} : Finset Var) ∪
          ((syn_wex (alpha_dummy_002 A B) (syn_wa (syn_wbr (Class.cv (alpha_dummy_000 A B)) B
                  (Class.cv (alpha_dummy_002 A B))) (syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                  (Class.cv (alpha_dummy_001 A B)))))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wex (alpha_dummy_002 A B) (syn_wa
                  (syn_wbr (Class.cv (alpha_dummy_000 A B)) B (Class.cv (alpha_dummy_002 A B)))
                  (syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                    (Class.cv (alpha_dummy_001 A B))))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => ((focused_notmem_0000 A B)) (h_eq ▸ hu)), (((fv_syn_wa
                      (syn_wbr (Class.cv (alpha_dummy_000 A B)) B
                        (Class.cv (alpha_dummy_002 A B)))
                      (syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                        (Class.cv (alpha_dummy_001 A B)))).symm ▸ (Finset.mem_union_left _
                    (((fv_syn_wbr (Class.cv (alpha_dummy_000 A B)) B
                          (Class.cv (alpha_dummy_002 A B))).symm ▸
                      (Finset.mem_union_right _ (hu)))))))⟩))))

theorem wpp_notmem_0196 (A : Class) (B : Class) : (alpha_dummy_003 A B) ∉ (B).fv := by
  exact (focused_notmem_0001 A B)

theorem focused_notmem_0002 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_B_z : z ∉ B.fv) : (alpha_dummy_004 x y z A B) ∉ B.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z
              (syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
                (syn_wbr (Class.cv z) A (Class.cv y))))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wex z
                (syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
                  (syn_wbr (Class.cv z) A (Class.cv y)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (dv_B_z) (h_eq ▸ hu)),
                (((fv_syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
                      (syn_wbr (Class.cv z) A (Class.cv y))).symm ▸ (Finset.mem_union_left _
                    (((fv_syn_wbr (Class.cv x) B (Class.cv z)).symm ▸
                      (Finset.mem_union_right _ (hu)))))))⟩))))

theorem wpp_notmem_0197 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_B_z : z ∉ B.fv) : (alpha_dummy_004 x y z A B) ∉ (B).fv := by
  exact (focused_notmem_0002 x y z A B dv_B_z)

theorem focused_notmem_0003 (A : Class) (B : Class) : (alpha_dummy_000 A B) ∉ B.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem wpp_notmem_0198 (A : Class) (B : Class) : (alpha_dummy_000 A B) ∉ (B).fv := by
  exact (focused_notmem_0003 A B)

theorem wpp_notmem_0199 (x : Var) (B : Class) (dv_B_x : x ∉ B.fv) : x ∉ (B).fv := by
  exact dv_B_x

theorem focused_notmem_0004 (A : Class) (B : Class) : (alpha_dummy_001 A B) ∉ B.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 1 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem wpp_notmem_0200 (A : Class) (B : Class) : (alpha_dummy_001 A B) ∉ (B).fv := by
  exact (focused_notmem_0004 A B)

theorem wpp_notmem_0201 (y : Var) (B : Class) (dv_B_y : y ∉ B.fv) : y ∉ (B).fv := by
  exact dv_B_y

theorem wpp_notmem_0202 (A : Class) (B : Class) : (alpha_dummy_002 A B) ∉ (B).fv := by
  exact (focused_notmem_0000 A B)

theorem wpp_notmem_0203 (z : Var) (B : Class) (dv_B_z : z ∉ B.fv) : z ∉ (B).fv := by
  exact dv_B_z

theorem focused_notmem_0005 (A : Class) (B : Class) : (alpha_dummy_002 A B) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_left _ (hu))

theorem focused_notmem_0006 (A : Class) (B : Class) : (alpha_dummy_003 A B) ∉ A.fv :=
  by
  change
    freshVar
        (({(alpha_dummy_000 A B)} : Finset Var) ∪ ({(alpha_dummy_001 A B)} : Finset Var) ∪
          ((syn_wex (alpha_dummy_002 A B) (syn_wa (syn_wbr (Class.cv (alpha_dummy_000 A B)) B
                  (Class.cv (alpha_dummy_002 A B))) (syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                  (Class.cv (alpha_dummy_001 A B)))))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wex (alpha_dummy_002 A B) (syn_wa
                  (syn_wbr (Class.cv (alpha_dummy_000 A B)) B (Class.cv (alpha_dummy_002 A B)))
                  (syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                    (Class.cv (alpha_dummy_001 A B))))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => ((focused_notmem_0005 A B)) (h_eq ▸ hu)), (((fv_syn_wa
                      (syn_wbr (Class.cv (alpha_dummy_000 A B)) B
                        (Class.cv (alpha_dummy_002 A B)))
                      (syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                        (Class.cv (alpha_dummy_001 A B)))).symm ▸ (Finset.mem_union_right _
                    (((fv_syn_wbr (Class.cv (alpha_dummy_002 A B)) A
                          (Class.cv (alpha_dummy_001 A B))).symm ▸
                      (Finset.mem_union_right _ (hu)))))))⟩))))

theorem wpp_notmem_0286 (A : Class) (B : Class) : (alpha_dummy_003 A B) ∉ (A).fv := by
  exact (focused_notmem_0006 A B)

theorem focused_notmem_0007 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) : (alpha_dummy_004 x y z A B) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z
              (syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
                (syn_wbr (Class.cv z) A (Class.cv y))))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wex z
                (syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
                  (syn_wbr (Class.cv z) A (Class.cv y)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (dv_A_z) (h_eq ▸ hu)),
                (((fv_syn_wa (syn_wbr (Class.cv x) B (Class.cv z))
                      (syn_wbr (Class.cv z) A (Class.cv y))).symm ▸ (Finset.mem_union_right _
                    (((fv_syn_wbr (Class.cv z) A (Class.cv y)).symm ▸
                      (Finset.mem_union_right _ (hu)))))))⟩))))

theorem wpp_notmem_0287 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) : (alpha_dummy_004 x y z A B) ∉ (A).fv := by
  exact (focused_notmem_0007 x y z A B dv_A_z)

theorem focused_notmem_0008 (A : Class) (B : Class) : (alpha_dummy_000 A B) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem wpp_notmem_0288 (A : Class) (B : Class) : (alpha_dummy_000 A B) ∉ (A).fv := by
  exact (focused_notmem_0008 A B)

theorem wpp_notmem_0289 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem focused_notmem_0009 (A : Class) (B : Class) : (alpha_dummy_001 A B) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (hu))

theorem wpp_notmem_0290 (A : Class) (B : Class) : (alpha_dummy_001 A B) ∉ (A).fv := by
  exact (focused_notmem_0009 A B)

theorem wpp_notmem_0291 (y : Var) (A : Class) (dv_A_y : y ∉ A.fv) : y ∉ (A).fv := by
  exact dv_A_y

theorem wpp_notmem_0292 (A : Class) (B : Class) : (alpha_dummy_002 A B) ∉ (A).fv := by
  exact (focused_notmem_0005 A B)

theorem wpp_notmem_0293 (z : Var) (A : Class) (dv_A_z : z ∉ A.fv) : z ∉ (A).fv := by
  exact dv_A_z

end CompositionAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
