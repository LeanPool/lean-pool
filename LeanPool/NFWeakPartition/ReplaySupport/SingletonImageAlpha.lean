/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001043SiReflected001. -/


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


namespace SingletonImageAlpha

@[expose]
def alpha_dummy_000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

@[expose]
def alpha_dummy_001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

@[expose]
def alpha_dummy_002 (A : Class) : Var :=
  (freshVar ((A).fv) 2)

@[expose]
def alpha_dummy_003 (A : Class) : Var :=
  (freshVar ((A).fv) 3)

@[expose]
def alpha_dummy_004 (A : Class) : Var :=
  (freshVar (({(alpha_dummy_001 A)} : Finset Var) ∪ ({(alpha_dummy_002 A)} : Finset Var) ∪
      ((syn_wex (alpha_dummy_003 A) (syn_wex (alpha_dummy_000 A) (syn_w3a
              (Wff.classEq (Class.cv (alpha_dummy_001 A))
                (syn_csn (Class.cv (alpha_dummy_003 A))))
              (Wff.classEq (Class.cv (alpha_dummy_002 A))
                (syn_csn (Class.cv (alpha_dummy_000 A))))
              (syn_wbr (Class.cv (alpha_dummy_003 A)) A (Class.cv (alpha_dummy_000 A))))))).fv)
    0)

@[expose]
def alpha_dummy_005 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z (syn_wex w
            (syn_w3a (Wff.classEq (Class.cv x) (syn_csn (Class.cv z)))
              (Wff.classEq (Class.cv y) (syn_csn (Class.cv w)))
              (syn_wbr (Class.cv z) A (Class.cv w)))))).fv) 0)

@[expose]
def alpha_dummy_006 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_001 A))).fv ∪ ((Class.cv (alpha_dummy_002 A))).fv) 0)

@[expose]
def alpha_dummy_007 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_001 A))).fv ∪ ((Class.cv (alpha_dummy_002 A))).fv) 1)

@[expose]
def alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
def alpha_dummy_009 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
def alpha_dummy_010 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_006 A)
            (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_001 A))
              (Wff.classEq (Class.cv (alpha_dummy_006 A))
                (syn_cphi (Class.cv (alpha_dummy_007 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_006 A)
            (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_002 A))
              (Wff.classEq (Class.cv (alpha_dummy_006 A))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_007 A))) (syn_csn (syn_c0c)))))))).fv)
    0)

@[expose]
def alpha_dummy_011 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_008 x y)
            (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                (syn_cphi (Class.cv (alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_012 (A : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_006 A)
          (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_001 A))
            (Wff.classEq (Class.cv (alpha_dummy_006 A))
              (syn_cphi (Class.cv (alpha_dummy_007 A))))))).fv ∪ ((Class.cab (alpha_dummy_006 A)
          (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_001 A))
            (Wff.classEq (Class.cv (alpha_dummy_006 A))
              (syn_cphi (Class.cv (alpha_dummy_007 A))))))).fv) 0)

@[expose]
def alpha_dummy_013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_008 x y))
              (syn_cphi (Class.cv (alpha_dummy_009 x y))))))).fv ∪
      ((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_008 x y))
              (syn_cphi (Class.cv (alpha_dummy_009 x y))))))).fv) 0)

@[expose]
def alpha_dummy_014 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_007 A))).fv) 0)

@[expose]
def alpha_dummy_015 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_007 A))).fv) 1)

@[expose]
def alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_009 x y))).fv) 0)

@[expose]
def alpha_dummy_017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_009 x y))).fv) 1)

@[expose]
def alpha_dummy_018 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_014 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_014 A)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_014 A))).fv) 0)

@[expose]
def alpha_dummy_019 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_016 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_016 x y)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_016 x y))).fv) 0)

@[expose]
def alpha_dummy_020 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_021 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_022 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_036 (A : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_006 A)
          (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_002 A))
            (Wff.classEq (Class.cv (alpha_dummy_006 A))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_007 A))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_006 A)
          (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_002 A))
            (Wff.classEq (Class.cv (alpha_dummy_006 A))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_007 A))) (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
def alpha_dummy_037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alpha_dummy_008 x y))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alpha_dummy_008 x y))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_038 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_007 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_039 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_009 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_040 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_007 A)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_007 A)))).fv) 0)

@[expose]
def alpha_dummy_041 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_009 x y)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_009 x y)))).fv) 0)

@[expose]
def alpha_dummy_046 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_003 A))).fv ∪ ((Class.cv (alpha_dummy_000 A))).fv) 0)

@[expose]
def alpha_dummy_047 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_003 A))).fv ∪ ((Class.cv (alpha_dummy_000 A))).fv) 1)

@[expose]
def alpha_dummy_048 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 0)

@[expose]
def alpha_dummy_049 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 1)

@[expose]
def alpha_dummy_050 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_046 A)
            (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_003 A))
              (Wff.classEq (Class.cv (alpha_dummy_046 A))
                (syn_cphi (Class.cv (alpha_dummy_047 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_046 A)
            (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_000 A))
              (Wff.classEq (Class.cv (alpha_dummy_046 A))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_047 A))) (syn_csn (syn_c0c)))))))).fv)
    0)

@[expose]
def alpha_dummy_051 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_048 z w)
            (syn_wrex (alpha_dummy_049 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                (syn_cphi (Class.cv (alpha_dummy_049 z w)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_049 z w)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_052 (A : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_046 A)
          (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_003 A))
            (Wff.classEq (Class.cv (alpha_dummy_046 A))
              (syn_cphi (Class.cv (alpha_dummy_047 A))))))).fv ∪ ((Class.cab (alpha_dummy_046 A)
          (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_003 A))
            (Wff.classEq (Class.cv (alpha_dummy_046 A))
              (syn_cphi (Class.cv (alpha_dummy_047 A))))))).fv) 0)

@[expose]
def alpha_dummy_053 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_048 z w))
              (syn_cphi (Class.cv (alpha_dummy_049 z w))))))).fv ∪
      ((Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_048 z w))
              (syn_cphi (Class.cv (alpha_dummy_049 z w))))))).fv) 0)

@[expose]
def alpha_dummy_054 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_047 A))).fv) 0)

@[expose]
def alpha_dummy_055 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_047 A))).fv) 1)

@[expose]
def alpha_dummy_056 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_049 z w))).fv) 0)

@[expose]
def alpha_dummy_057 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_049 z w))).fv) 1)

@[expose]
def alpha_dummy_058 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_054 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_054 A)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_054 A))).fv) 0)

@[expose]
def alpha_dummy_059 (z : Var) (w : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_056 z w)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_056 z w)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_056 z w))).fv) 0)

@[expose]
def alpha_dummy_060 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_061 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_062 (A : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_063 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_064 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_065 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_076 (A : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_046 A)
          (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_000 A))
            (Wff.classEq (Class.cv (alpha_dummy_046 A))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_047 A))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_046 A)
          (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_000 A))
            (Wff.classEq (Class.cv (alpha_dummy_046 A))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_047 A))) (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
def alpha_dummy_077 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alpha_dummy_048 z w))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_049 z w))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alpha_dummy_048 z w))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_049 z w))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_078 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_047 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_079 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_049 z w))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_080 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_047 A)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_047 A)))).fv) 0)

@[expose]
def alpha_dummy_081 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_049 z w)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_049 z w)))).fv) 0)

theorem mem_pair_support_left (u v : Var) (support : Finset Var) :
    u ∈ ({ u } ∪ { v } ∪ support) :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))

theorem mem_pair_support_right (u v : Var) (support : Finset Var) :
    v ∈ ({ u } ∪ { v } ∪ support) :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem support_mem_0000 (A : Class) :
    (alpha_dummy_001 A) ∈
      (({(alpha_dummy_001 A)} : Finset Var) ∪ ({(alpha_dummy_002 A)} : Finset Var) ∪
        ((syn_wex (alpha_dummy_003 A) (syn_wex (alpha_dummy_000 A) (syn_w3a
                (Wff.classEq (Class.cv (alpha_dummy_001 A))
                  (syn_csn (Class.cv (alpha_dummy_003 A))))
                (Wff.classEq (Class.cv (alpha_dummy_002 A))
                  (syn_csn (Class.cv (alpha_dummy_000 A))))
                (syn_wbr (Class.cv (alpha_dummy_003 A)) A
                  (Class.cv (alpha_dummy_000 A))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_left (alpha_dummy_001 A) (alpha_dummy_002 A)
        ((syn_wex (alpha_dummy_003 A) (syn_wex (alpha_dummy_000 A) (syn_w3a
                (Wff.classEq (Class.cv (alpha_dummy_001 A))
                  (syn_csn (Class.cv (alpha_dummy_003 A))))
                (Wff.classEq (Class.cv (alpha_dummy_002 A))
                  (syn_csn (Class.cv (alpha_dummy_000 A))))
                (syn_wbr (Class.cv (alpha_dummy_003 A)) A (Class.cv (alpha_dummy_000 A))))))).fv

theorem support_mem_0001 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z (syn_wex w
              (syn_w3a (Wff.classEq (Class.cv x) (syn_csn (Class.cv z)))
                (Wff.classEq (Class.cv y) (syn_csn (Class.cv w)))
                (syn_wbr (Class.cv z) A (Class.cv w)))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_left x y
        ((syn_wex z (syn_wex w (syn_w3a (Wff.classEq (Class.cv x) (syn_csn (Class.cv z)))
                (Wff.classEq (Class.cv y) (syn_csn (Class.cv w)))
                (syn_wbr (Class.cv z) A (Class.cv w)))))).fv

theorem support_mem_0002 (A : Class) :
    (alpha_dummy_002 A) ∈
      (({(alpha_dummy_001 A)} : Finset Var) ∪ ({(alpha_dummy_002 A)} : Finset Var) ∪
        ((syn_wex (alpha_dummy_003 A) (syn_wex (alpha_dummy_000 A) (syn_w3a
                (Wff.classEq (Class.cv (alpha_dummy_001 A))
                  (syn_csn (Class.cv (alpha_dummy_003 A))))
                (Wff.classEq (Class.cv (alpha_dummy_002 A))
                  (syn_csn (Class.cv (alpha_dummy_000 A))))
                (syn_wbr (Class.cv (alpha_dummy_003 A)) A
                  (Class.cv (alpha_dummy_000 A))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_right (alpha_dummy_001 A) (alpha_dummy_002 A)
        ((syn_wex (alpha_dummy_003 A) (syn_wex (alpha_dummy_000 A) (syn_w3a
                (Wff.classEq (Class.cv (alpha_dummy_001 A))
                  (syn_csn (Class.cv (alpha_dummy_003 A))))
                (Wff.classEq (Class.cv (alpha_dummy_002 A))
                  (syn_csn (Class.cv (alpha_dummy_000 A))))
                (syn_wbr (Class.cv (alpha_dummy_003 A)) A (Class.cv (alpha_dummy_000 A))))))).fv

theorem support_mem_0003 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z (syn_wex w
              (syn_w3a (Wff.classEq (Class.cv x) (syn_csn (Class.cv z)))
                (Wff.classEq (Class.cv y) (syn_csn (Class.cv w)))
                (syn_wbr (Class.cv z) A (Class.cv w)))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_right x y
        ((syn_wex z (syn_wex w (syn_w3a (Wff.classEq (Class.cv x) (syn_csn (Class.cv z)))
                (Wff.classEq (Class.cv y) (syn_csn (Class.cv w)))
                (syn_wbr (Class.cv z) A (Class.cv w)))))).fv

theorem support_mem_0004 (A : Class) :
    (alpha_dummy_001 A) ∈
      (((Class.cv (alpha_dummy_001 A))).fv ∪ ((Class.cv (alpha_dummy_002 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0005 (A : Class) :
    (alpha_dummy_001 A) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_006 A)
              (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_001 A))
                (Wff.classEq (Class.cv (alpha_dummy_006 A))
                  (syn_cphi (Class.cv (alpha_dummy_007 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_006 A)
              (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_002 A))
                (Wff.classEq (Class.cv (alpha_dummy_006 A))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_007 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A) 1))
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
      (((syn_ccompl (Class.cab (alpha_dummy_008 x y)
              (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
                (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv y)
                (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_009 x y)))
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

theorem support_mem_0008 (A : Class) :
    (alpha_dummy_001 A) ∈
      (((Class.cab (alpha_dummy_006 A)
            (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_001 A))
              (Wff.classEq (Class.cv (alpha_dummy_006 A))
                (syn_cphi (Class.cv (alpha_dummy_007 A))))))).fv ∪
        ((Class.cab (alpha_dummy_006 A)
            (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_001 A))
              (Wff.classEq (Class.cv (alpha_dummy_006 A))
                (syn_cphi (Class.cv (alpha_dummy_007 A))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                (syn_cphi (Class.cv (alpha_dummy_009 x y))))))).fv ∪
        ((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                (syn_cphi (Class.cv (alpha_dummy_009 x y))))))).fv) :=
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

theorem support_mem_0010 (A : Class) :
    (alpha_dummy_007 A) ∈ (((Class.cv (alpha_dummy_007 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0011 (x : Var) (y : Var) :
    (alpha_dummy_009 x y) ∈ (((Class.cv (alpha_dummy_009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0012 (A : Class) :
    (alpha_dummy_014 A) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_014 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_014 A)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_014 A))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0013 (x : Var) (y : Var) :
    (alpha_dummy_016 x y) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_016 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_016 x y)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_016 x y))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0014 (A : Class) :
    (alpha_dummy_014 A) ∈ (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0015 (x : Var) (y : Var) :
    (alpha_dummy_016 x y) ∈ (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0016 (A : Class) :
    (alpha_dummy_021 A) ∈
      (((syn_cnin (Class.cv (alpha_dummy_021 A)) (Class.cv (alpha_dummy_022 A)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_021 A)) (Class.cv (alpha_dummy_022 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0017 (x : Var) (y : Var) :
    (alpha_dummy_024 x y) ∈
      (((syn_cnin (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0018 (A : Class) :
    (alpha_dummy_021 A) ∈
      (((Class.cv (alpha_dummy_021 A))).fv ∪ ((Class.cv (alpha_dummy_022 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0019 (x : Var) (y : Var) :
    (alpha_dummy_024 x y) ∈
      (((Class.cv (alpha_dummy_024 x y))).fv ∪ ((Class.cv (alpha_dummy_025 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0020 (A : Class) :
    (alpha_dummy_022 A) ∈
      (((syn_cnin (Class.cv (alpha_dummy_021 A)) (Class.cv (alpha_dummy_022 A)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_021 A)) (Class.cv (alpha_dummy_022 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0021 (x : Var) (y : Var) :
    (alpha_dummy_025 x y) ∈
      (((syn_cnin (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0022 (A : Class) :
    (alpha_dummy_022 A) ∈
      (((Class.cv (alpha_dummy_021 A))).fv ∪ ((Class.cv (alpha_dummy_022 A))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0023 (x : Var) (y : Var) :
    (alpha_dummy_025 x y) ∈
      (((Class.cv (alpha_dummy_024 x y))).fv ∪ ((Class.cv (alpha_dummy_025 x y))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0024 (A : Class) :
    (alpha_dummy_021 A) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_021 A)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_022 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0025 (x : Var) (y : Var) :
    (alpha_dummy_024 x y) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_024 x y)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_025 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0026 (A : Class) :
    (alpha_dummy_021 A) ∈
      (((Class.cv (alpha_dummy_021 A))).fv ∪ ((Class.cv (alpha_dummy_021 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0027 (x : Var) (y : Var) :
    (alpha_dummy_024 x y) ∈
      (((Class.cv (alpha_dummy_024 x y))).fv ∪ ((Class.cv (alpha_dummy_024 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0028 (A : Class) :
    (alpha_dummy_022 A) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_021 A)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_022 A)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0029 (x : Var) (y : Var) :
    (alpha_dummy_025 x y) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_024 x y)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_025 x y)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0030 (A : Class) :
    (alpha_dummy_022 A) ∈
      (((Class.cv (alpha_dummy_022 A))).fv ∪ ((Class.cv (alpha_dummy_022 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0031 (x : Var) (y : Var) :
    (alpha_dummy_025 x y) ∈
      (((Class.cv (alpha_dummy_025 x y))).fv ∪ ((Class.cv (alpha_dummy_025 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0032 (A : Class) :
    (alpha_dummy_002 A) ∈
      (((Class.cv (alpha_dummy_001 A))).fv ∪ ((Class.cv (alpha_dummy_002 A))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0033 (A : Class) :
    (alpha_dummy_002 A) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_006 A)
              (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_001 A))
                (Wff.classEq (Class.cv (alpha_dummy_006 A))
                  (syn_cphi (Class.cv (alpha_dummy_007 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_006 A)
              (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_002 A))
                (Wff.classEq (Class.cv (alpha_dummy_006 A))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_007 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 1))
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
      (((syn_ccompl (Class.cab (alpha_dummy_008 x y)
              (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
                (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv y)
                (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_009 x y)))
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

theorem support_mem_0036 (A : Class) :
    (alpha_dummy_002 A) ∈
      (((Class.cab (alpha_dummy_006 A)
            (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_002 A))
              (Wff.classEq (Class.cv (alpha_dummy_006 A))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_007 A))) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (alpha_dummy_006 A)
            (syn_wrex (alpha_dummy_007 A) (Class.cv (alpha_dummy_002 A))
              (Wff.classEq (Class.cv (alpha_dummy_006 A))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_007 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0037 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_008 x y)
            (syn_wrex (alpha_dummy_009 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_009 x y)))
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

theorem support_mem_0038 (A : Class) :
    (alpha_dummy_007 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_007 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0039 (x : Var) (y : Var) :
    (alpha_dummy_009 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0040 (A : Class) :
    (alpha_dummy_007 A) ∈
      (((syn_cphi (Class.cv (alpha_dummy_007 A)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_007 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0041 (x : Var) (y : Var) :
    (alpha_dummy_009 x y) ∈
      (((syn_cphi (Class.cv (alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_009 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0042 (A : Class) :
    (alpha_dummy_003 A) ∈ (((Class.cv (alpha_dummy_003 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0043 (z : Var) : z ∈ (((Class.cv z)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0044 (A : Class) :
    (alpha_dummy_000 A) ∈ (((Class.cv (alpha_dummy_000 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0045 (w : Var) : w ∈ (((Class.cv w)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0046 (A : Class) :
    (alpha_dummy_003 A) ∈
      (((Class.cv (alpha_dummy_003 A))).fv ∪ ((Class.cv (alpha_dummy_000 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0047 (A : Class) :
    (alpha_dummy_003 A) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_046 A)
              (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_003 A))
                (Wff.classEq (Class.cv (alpha_dummy_046 A))
                  (syn_cphi (Class.cv (alpha_dummy_047 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_046 A)
              (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_000 A))
                (Wff.classEq (Class.cv (alpha_dummy_046 A))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_047 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0048 (z : Var) (w : Var) :
    z ∈ (((Class.cv z)).fv ∪ ((Class.cv w)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0049 (z : Var) (w : Var) :
    z ∈
      (((syn_ccompl (Class.cab (alpha_dummy_048 z w)
              (syn_wrex (alpha_dummy_049 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                  (syn_cphi (Class.cv (alpha_dummy_049 z w)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_049 z w)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0050 (A : Class) :
    (alpha_dummy_003 A) ∈
      (((Class.cab (alpha_dummy_046 A)
            (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_003 A))
              (Wff.classEq (Class.cv (alpha_dummy_046 A))
                (syn_cphi (Class.cv (alpha_dummy_047 A))))))).fv ∪
        ((Class.cab (alpha_dummy_046 A)
            (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_003 A))
              (Wff.classEq (Class.cv (alpha_dummy_046 A))
                (syn_cphi (Class.cv (alpha_dummy_047 A))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0051 (z : Var) (w : Var) :
    z ∈
      (((Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                (syn_cphi (Class.cv (alpha_dummy_049 z w))))))).fv ∪
        ((Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                (syn_cphi (Class.cv (alpha_dummy_049 z w))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0052 (A : Class) :
    (alpha_dummy_047 A) ∈ (((Class.cv (alpha_dummy_047 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0053 (z : Var) (w : Var) :
    (alpha_dummy_049 z w) ∈ (((Class.cv (alpha_dummy_049 z w))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0054 (A : Class) :
    (alpha_dummy_054 A) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_054 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_054 A)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_054 A))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0055 (z : Var) (w : Var) :
    (alpha_dummy_056 z w) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_056 z w)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_056 z w)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_056 z w))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0056 (A : Class) :
    (alpha_dummy_054 A) ∈ (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0057 (z : Var) (w : Var) :
    (alpha_dummy_056 z w) ∈ (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0058 (A : Class) :
    (alpha_dummy_061 A) ∈
      (((syn_cnin (Class.cv (alpha_dummy_061 A)) (Class.cv (alpha_dummy_062 A)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_061 A)) (Class.cv (alpha_dummy_062 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0059 (z : Var) (w : Var) :
    (alpha_dummy_064 z w) ∈
      (((syn_cnin (Class.cv (alpha_dummy_064 z w)) (Class.cv (alpha_dummy_065 z w)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_064 z w)) (Class.cv (alpha_dummy_065 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0060 (A : Class) :
    (alpha_dummy_061 A) ∈
      (((Class.cv (alpha_dummy_061 A))).fv ∪ ((Class.cv (alpha_dummy_062 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0061 (z : Var) (w : Var) :
    (alpha_dummy_064 z w) ∈
      (((Class.cv (alpha_dummy_064 z w))).fv ∪ ((Class.cv (alpha_dummy_065 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0062 (A : Class) :
    (alpha_dummy_062 A) ∈
      (((syn_cnin (Class.cv (alpha_dummy_061 A)) (Class.cv (alpha_dummy_062 A)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_061 A)) (Class.cv (alpha_dummy_062 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0063 (z : Var) (w : Var) :
    (alpha_dummy_065 z w) ∈
      (((syn_cnin (Class.cv (alpha_dummy_064 z w)) (Class.cv (alpha_dummy_065 z w)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_064 z w)) (Class.cv (alpha_dummy_065 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0064 (A : Class) :
    (alpha_dummy_062 A) ∈
      (((Class.cv (alpha_dummy_061 A))).fv ∪ ((Class.cv (alpha_dummy_062 A))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0065 (z : Var) (w : Var) :
    (alpha_dummy_065 z w) ∈
      (((Class.cv (alpha_dummy_064 z w))).fv ∪ ((Class.cv (alpha_dummy_065 z w))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0066 (A : Class) :
    (alpha_dummy_061 A) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_061 A)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_062 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0067 (z : Var) (w : Var) :
    (alpha_dummy_064 z w) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_064 z w)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_065 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0068 (A : Class) :
    (alpha_dummy_061 A) ∈
      (((Class.cv (alpha_dummy_061 A))).fv ∪ ((Class.cv (alpha_dummy_061 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0069 (z : Var) (w : Var) :
    (alpha_dummy_064 z w) ∈
      (((Class.cv (alpha_dummy_064 z w))).fv ∪ ((Class.cv (alpha_dummy_064 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0070 (A : Class) :
    (alpha_dummy_062 A) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_061 A)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_062 A)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0071 (z : Var) (w : Var) :
    (alpha_dummy_065 z w) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_064 z w)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_065 z w)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0072 (A : Class) :
    (alpha_dummy_062 A) ∈
      (((Class.cv (alpha_dummy_062 A))).fv ∪ ((Class.cv (alpha_dummy_062 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0073 (z : Var) (w : Var) :
    (alpha_dummy_065 z w) ∈
      (((Class.cv (alpha_dummy_065 z w))).fv ∪ ((Class.cv (alpha_dummy_065 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0074 (A : Class) :
    (alpha_dummy_000 A) ∈
      (((Class.cv (alpha_dummy_003 A))).fv ∪ ((Class.cv (alpha_dummy_000 A))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0075 (A : Class) :
    (alpha_dummy_000 A) ∈
      (((syn_ccompl (Class.cab (alpha_dummy_046 A)
              (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_003 A))
                (Wff.classEq (Class.cv (alpha_dummy_046 A))
                  (syn_cphi (Class.cv (alpha_dummy_047 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_046 A)
              (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_000 A))
                (Wff.classEq (Class.cv (alpha_dummy_046 A))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_047 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0076 (z : Var) (w : Var) :
    w ∈ (((Class.cv z)).fv ∪ ((Class.cv w)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0077 (z : Var) (w : Var) :
    w ∈
      (((syn_ccompl (Class.cab (alpha_dummy_048 z w)
              (syn_wrex (alpha_dummy_049 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                  (syn_cphi (Class.cv (alpha_dummy_049 z w)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_049 z w)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0078 (A : Class) :
    (alpha_dummy_000 A) ∈
      (((Class.cab (alpha_dummy_046 A)
            (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_000 A))
              (Wff.classEq (Class.cv (alpha_dummy_046 A))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_047 A))) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (alpha_dummy_046 A)
            (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_000 A))
              (Wff.classEq (Class.cv (alpha_dummy_046 A))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_047 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0079 (z : Var) (w : Var) :
    w ∈
      (((Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_049 z w)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_048 z w)
            (syn_wrex (alpha_dummy_049 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_049 z w)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0080 (A : Class) :
    (alpha_dummy_047 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_047 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0081 (z : Var) (w : Var) :
    (alpha_dummy_049 z w) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_049 z w))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0082 (A : Class) :
    (alpha_dummy_047 A) ∈
      (((syn_cphi (Class.cv (alpha_dummy_047 A)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_047 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0083 (z : Var) (w : Var) :
    (alpha_dummy_049 z w) ∈
      (((syn_cphi (Class.cv (alpha_dummy_049 z w)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_049 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem focused_notmem_0000 (A : Class) : (alpha_dummy_000 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => hu)

theorem focused_notmem_0001 (A : Class) : (alpha_dummy_003 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 3 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 3
      (fun u hu => hu)

theorem parameter_support (x y z w : Var) (A : Class) (hz : z ∉ A.fv) (hw : w ∉ A.fv) :
    ∀ ⦃u : Var⦄,
      u ∈ A.fv →
        u ∈
          (syn_wex z (syn_wex w (syn_w3a (Wff.classEq (Class.cv x) (syn_csn (Class.cv z)))
                  (Wff.classEq (Class.cv y) (syn_csn (Class.cv w)))
                  (syn_wbr (Class.cv z) A (Class.cv w))))).fv :=
  by
  rw [fv_syn_wex, fv_syn_wex, fv_syn_w3a, fv_syn_wbr]
  intro u hu
  exact
    Finset.mem_erase.mpr
      ⟨(fun h => hz (h ▸ hu)),
        Finset.mem_erase.mpr
          ⟨(fun h => hw (h ▸ hu)),
            Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ hu))⟩⟩

theorem focused_notmem_0002 (A : Class) : (alpha_dummy_004 A) ∉ A.fv :=
  by
  unfold alpha_dummy_004
  with_reducible
    exact
      (NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu =>
          Finset.mem_union_right _
            (parameter_support (alpha_dummy_001 A) (alpha_dummy_002 A) (alpha_dummy_003 A)
              (alpha_dummy_000 A) A (focused_notmem_0001 A) (focused_notmem_0000 A) hu)))

theorem wpp_notmem_0204 (A : Class) : (alpha_dummy_004 A) ∉ (A).fv := by
  exact (focused_notmem_0002 A)

theorem focused_notmem_0003 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_A_w : w ∉ A.fv) (dv_A_z : z ∉ A.fv) : (alpha_dummy_005 x y z w A) ∉ A.fv :=
  by
  unfold alpha_dummy_005
  with_reducible
    exact
      (NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu =>
          Finset.mem_union_right _ (parameter_support x y z w A dv_A_z dv_A_w hu)))

theorem wpp_notmem_0205 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_A_w : w ∉ A.fv) (dv_A_z : z ∉ A.fv) : (alpha_dummy_005 x y z w A) ∉ (A).fv := by
  exact (focused_notmem_0003 x y z w A dv_A_w dv_A_z)

theorem focused_notmem_0004 (A : Class) : (alpha_dummy_001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => hu)

theorem wpp_notmem_0206 (A : Class) : (alpha_dummy_001 A) ∉ (A).fv := by
  exact (focused_notmem_0004 A)

theorem wpp_notmem_0207 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem focused_notmem_0005 (A : Class) : (alpha_dummy_002 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => hu)

theorem wpp_notmem_0208 (A : Class) : (alpha_dummy_002 A) ∉ (A).fv := by
  exact (focused_notmem_0005 A)

theorem wpp_notmem_0209 (y : Var) (A : Class) (dv_A_y : y ∉ A.fv) : y ∉ (A).fv := by
  exact dv_A_y

theorem wpp_notmem_0210 (A : Class) : (alpha_dummy_003 A) ∉ (A).fv := by
  exact (focused_notmem_0001 A)

theorem wpp_notmem_0211 (z : Var) (A : Class) (dv_A_z : z ∉ A.fv) : z ∉ (A).fv := by
  exact dv_A_z

theorem wpp_notmem_0212 (A : Class) : (alpha_dummy_000 A) ∉ (A).fv := by
  exact (focused_notmem_0000 A)

theorem wpp_notmem_0213 (w : Var) (A : Class) (dv_A_w : w ∉ A.fv) : w ∉ (A).fv := by
  exact dv_A_w

end SingletonImageAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
