/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001039SwapReflected001. -/


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

/-! Shared variable, support, and alpha-certificate components for swap. -/


namespace SwapAlpha

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
  (freshVar ((∅ : Finset Var)) 3)

@[expose]
def alpha_dummy_004 : Var :=
  (freshVar (({ alpha_dummy_001 } : Finset Var) ∪ ({ alpha_dummy_002 } : Finset Var) ∪
      ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa
              (Wff.classEq (Class.cv alpha_dummy_001)
                (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000)))
              (Wff.classEq (Class.cv alpha_dummy_002)
                (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_003))))))).fv) 0)

@[expose]
def alpha_dummy_005 (x : Var) (y : Var) (z : Var) (w : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z (syn_wex w
            (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w)))
              (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv) 0)

@[expose]
def alpha_dummy_006 : Var :=
  (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0)

@[expose]
def alpha_dummy_007 : Var :=
  (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 1)

@[expose]
def alpha_dummy_008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
def alpha_dummy_009 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
def alpha_dummy_010 : Var :=
  (freshVar (((syn_ccompl (Class.cab alpha_dummy_006
            (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl
          (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c)))))))).fv) 0)

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
def alpha_dummy_012 : Var :=
  (freshVar (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001)
            (Wff.classEq (Class.cv alpha_dummy_006)
              (syn_cphi (Class.cv alpha_dummy_007)))))).fv ∪ ((Class.cab alpha_dummy_006
          (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001)
            (Wff.classEq (Class.cv alpha_dummy_006)
              (syn_cphi (Class.cv alpha_dummy_007)))))).fv) 0)

@[expose]
def alpha_dummy_013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_008 x y))
              (syn_cphi (Class.cv (alpha_dummy_009 x y))))))).fv ∪
      ((Class.cab (alpha_dummy_008 x y) (syn_wrex (alpha_dummy_009 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alpha_dummy_008 x y))
              (syn_cphi (Class.cv (alpha_dummy_009 x y))))))).fv) 0)

@[expose]
def alpha_dummy_014 : Var :=
  (freshVar (((Class.cv alpha_dummy_007)).fv) 0)

@[expose]
def alpha_dummy_015 : Var :=
  (freshVar (((Class.cv alpha_dummy_007)).fv) 1)

@[expose]
def alpha_dummy_016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_009 x y))).fv) 0)

@[expose]
def alpha_dummy_017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_009 x y))).fv) 1)

@[expose]
def alpha_dummy_018 : Var :=
  (freshVar (((Wff.classMem (Class.cv alpha_dummy_014) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_014)).fv)
    0)

@[expose]
def alpha_dummy_019 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_016 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_016 x y)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_016 x y))).fv) 0)

@[expose]
def alpha_dummy_020 : Var :=
  (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_021 : Var :=
  (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_022 : Var :=
  (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 2)

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
def alpha_dummy_036 : Var :=
  (freshVar (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002)
            (Wff.classEq (Class.cv alpha_dummy_006)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002)
            (Wff.classEq (Class.cv alpha_dummy_006)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv) 0)

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
def alpha_dummy_038 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_007)))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_039 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_009 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_040 : Var :=
  (freshVar (((syn_cphi (Class.cv alpha_dummy_007))).fv ∪
      ((syn_cphi (Class.cv alpha_dummy_007))).fv) 0)

@[expose]
def alpha_dummy_041 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_009 x y)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_009 x y)))).fv) 0)

@[expose]
def alpha_dummy_042 : Var :=
  (freshVar (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0)

@[expose]
def alpha_dummy_043 : Var :=
  (freshVar (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1)

@[expose]
def alpha_dummy_044 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 0)

@[expose]
def alpha_dummy_045 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 1)

@[expose]
def alpha_dummy_046 : Var :=
  (freshVar (((syn_ccompl (Class.cab alpha_dummy_042
            (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl
          (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_047 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_044 z w)
            (syn_wrex (alpha_dummy_045 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                (syn_cphi (Class.cv (alpha_dummy_045 z w)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_045 z w)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_048 : Var :=
  (freshVar (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003)
            (Wff.classEq (Class.cv alpha_dummy_042)
              (syn_cphi (Class.cv alpha_dummy_043)))))).fv ∪ ((Class.cab alpha_dummy_042
          (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003)
            (Wff.classEq (Class.cv alpha_dummy_042)
              (syn_cphi (Class.cv alpha_dummy_043)))))).fv) 0)

@[expose]
def alpha_dummy_049 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_044 z w))
              (syn_cphi (Class.cv (alpha_dummy_045 z w))))))).fv ∪
      ((Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_044 z w))
              (syn_cphi (Class.cv (alpha_dummy_045 z w))))))).fv) 0)

@[expose]
def alpha_dummy_050 : Var :=
  (freshVar (((Class.cv alpha_dummy_043)).fv) 0)

@[expose]
def alpha_dummy_051 : Var :=
  (freshVar (((Class.cv alpha_dummy_043)).fv) 1)

@[expose]
def alpha_dummy_052 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_045 z w))).fv) 0)

@[expose]
def alpha_dummy_053 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_045 z w))).fv) 1)

@[expose]
def alpha_dummy_054 : Var :=
  (freshVar (((Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv alpha_dummy_050) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_050)).fv)
    0)

@[expose]
def alpha_dummy_055 (z : Var) (w : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_052 z w)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_052 z w)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_052 z w))).fv) 0)

@[expose]
def alpha_dummy_056 : Var :=
  (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_057 : Var :=
  (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_058 : Var :=
  (freshVar (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_059 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_060 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_061 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_072 : Var :=
  (freshVar (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000)
            (Wff.classEq (Class.cv alpha_dummy_042)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000)
            (Wff.classEq (Class.cv alpha_dummy_042)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
def alpha_dummy_073 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alpha_dummy_044 z w))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_045 z w))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alpha_dummy_044 z w))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_045 z w))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_074 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_043)))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_075 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_045 z w))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_076 : Var :=
  (freshVar (((syn_cphi (Class.cv alpha_dummy_043))).fv ∪
      ((syn_cphi (Class.cv alpha_dummy_043))).fv) 0)

@[expose]
def alpha_dummy_077 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_045 z w)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_045 z w)))).fv) 0)

@[expose]
def alpha_dummy_078 : Var :=
  (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) 0)

@[expose]
def alpha_dummy_079 : Var :=
  (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) 1)

@[expose]
def alpha_dummy_080 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv w)).fv ∪ ((Class.cv z)).fv) 0)

@[expose]
def alpha_dummy_081 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv w)).fv ∪ ((Class.cv z)).fv) 1)

@[expose]
def alpha_dummy_082 : Var :=
  (freshVar (((syn_ccompl (Class.cab alpha_dummy_078
            (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_078)
                (syn_cphi (Class.cv alpha_dummy_079))))))).fv ∪ ((syn_ccompl
          (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003)
              (Wff.classEq (Class.cv alpha_dummy_078)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_083 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (alpha_dummy_080 z w)
            (syn_wrex (alpha_dummy_081 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                (syn_cphi (Class.cv (alpha_dummy_081 z w)))))))).fv ∪ ((syn_ccompl
          (Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_081 z w)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
def alpha_dummy_084 : Var :=
  (freshVar (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000)
            (Wff.classEq (Class.cv alpha_dummy_078)
              (syn_cphi (Class.cv alpha_dummy_079)))))).fv ∪ ((Class.cab alpha_dummy_078
          (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000)
            (Wff.classEq (Class.cv alpha_dummy_078)
              (syn_cphi (Class.cv alpha_dummy_079)))))).fv) 0)

@[expose]
def alpha_dummy_085 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alpha_dummy_080 z w))
              (syn_cphi (Class.cv (alpha_dummy_081 z w))))))).fv ∪
      ((Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alpha_dummy_080 z w))
              (syn_cphi (Class.cv (alpha_dummy_081 z w))))))).fv) 0)

@[expose]
def alpha_dummy_086 : Var :=
  (freshVar (((Class.cv alpha_dummy_079)).fv) 0)

@[expose]
def alpha_dummy_087 : Var :=
  (freshVar (((Class.cv alpha_dummy_079)).fv) 1)

@[expose]
def alpha_dummy_088 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_081 z w))).fv) 0)

@[expose]
def alpha_dummy_089 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_081 z w))).fv) 1)

@[expose]
def alpha_dummy_090 : Var :=
  (freshVar (((Wff.classMem (Class.cv alpha_dummy_086) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv alpha_dummy_086) (syn_c1c))).fv ∪ ((Class.cv alpha_dummy_086)).fv)
    0)

@[expose]
def alpha_dummy_091 (z : Var) (w : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alpha_dummy_088 z w)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (alpha_dummy_088 z w)) (syn_c1c))).fv ∪
      ((Class.cv (alpha_dummy_088 z w))).fv) 0)

@[expose]
def alpha_dummy_092 : Var :=
  (freshVar (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_093 : Var :=
  (freshVar (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_094 : Var :=
  (freshVar (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_095 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_096 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_097 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_108 : Var :=
  (freshVar (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003)
            (Wff.classEq (Class.cv alpha_dummy_078)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003)
            (Wff.classEq (Class.cv alpha_dummy_078)
              (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
def alpha_dummy_109 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_080 z w))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_081 z w))) (syn_csn (syn_c0c))))))).fv ∪
      ((Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alpha_dummy_080 z w))
              (syn_cun (syn_cphi (Class.cv (alpha_dummy_081 z w))) (syn_csn (syn_c0c))))))).fv)
    0)

@[expose]
def alpha_dummy_110 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_079)))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_111 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_081 z w))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
def alpha_dummy_112 : Var :=
  (freshVar (((syn_cphi (Class.cv alpha_dummy_079))).fv ∪
      ((syn_cphi (Class.cv alpha_dummy_079))).fv) 0)

@[expose]
def alpha_dummy_113 (z : Var) (w : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (alpha_dummy_081 z w)))).fv ∪
      ((syn_cphi (Class.cv (alpha_dummy_081 z w)))).fv) 0)

theorem mem_pair_support_left (u v : Var) (support : Finset Var) :
    u ∈ ({ u } ∪ { v } ∪ support) :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))

theorem mem_pair_support_right (u v : Var) (support : Finset Var) :
    v ∈ ({ u } ∪ { v } ∪ support) :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem support_mem_0000 :
    alpha_dummy_001 ∈
      (({ alpha_dummy_001 } : Finset Var) ∪ ({ alpha_dummy_002 } : Finset Var) ∪
        ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa
                (Wff.classEq (Class.cv alpha_dummy_001)
                  (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000)))
                (Wff.classEq (Class.cv alpha_dummy_002) (syn_cop (Class.cv alpha_dummy_000)
                    (Class.cv alpha_dummy_003))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_left alpha_dummy_001 alpha_dummy_002
        ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa
                (Wff.classEq (Class.cv alpha_dummy_001)
                  (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000)))
                (Wff.classEq (Class.cv alpha_dummy_002)
                  (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_003))))))).fv

theorem support_mem_0001 (x : Var) (y : Var) (z : Var) (w : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z (syn_wex w
              (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w)))
                (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_left x y
        ((syn_wex z (syn_wex w
              (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w)))
                (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv

theorem support_mem_0002 :
    alpha_dummy_002 ∈
      (({ alpha_dummy_001 } : Finset Var) ∪ ({ alpha_dummy_002 } : Finset Var) ∪
        ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa
                (Wff.classEq (Class.cv alpha_dummy_001)
                  (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000)))
                (Wff.classEq (Class.cv alpha_dummy_002) (syn_cop (Class.cv alpha_dummy_000)
                    (Class.cv alpha_dummy_003))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_right alpha_dummy_001 alpha_dummy_002
        ((syn_wex alpha_dummy_003 (syn_wex alpha_dummy_000 (syn_wa
                (Wff.classEq (Class.cv alpha_dummy_001)
                  (syn_cop (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_000)))
                (Wff.classEq (Class.cv alpha_dummy_002)
                  (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_003))))))).fv

theorem support_mem_0003 (x : Var) (y : Var) (z : Var) (w : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((syn_wex z (syn_wex w
              (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w)))
                (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_right x y
        ((syn_wex z (syn_wex w
              (syn_wa (Wff.classEq (Class.cv x) (syn_cop (Class.cv z) (Class.cv w)))
                (Wff.classEq (Class.cv y) (syn_cop (Class.cv w) (Class.cv z))))))).fv

theorem support_mem_0004 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0005 :
    alpha_dummy_001 ∈
      (((syn_ccompl (Class.cab alpha_dummy_006
              (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_007))
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

theorem support_mem_0008 :
    alpha_dummy_001 ∈
      (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cphi (Class.cv alpha_dummy_007)))))).fv ∪ ((Class.cab alpha_dummy_006
            (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cphi (Class.cv alpha_dummy_007)))))).fv) :=
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

theorem support_mem_0010 : alpha_dummy_007 ∈ (((Class.cv alpha_dummy_007)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0011 (x : Var) (y : Var) :
    (alpha_dummy_009 x y) ∈ (((Class.cv (alpha_dummy_009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0012 :
    alpha_dummy_014 ∈
      (((Wff.classMem (Class.cv alpha_dummy_014) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_014)).fv) :=
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

theorem support_mem_0014 :
    alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) :=
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

theorem support_mem_0016 :
    alpha_dummy_021 ∈
      (((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv) :=
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

theorem support_mem_0018 :
    alpha_dummy_021 ∈
      (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_022)).fv) :=
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

theorem support_mem_0020 :
    alpha_dummy_022 ∈
      (((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))).fv) :=
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

theorem support_mem_0022 :
    alpha_dummy_022 ∈
      (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_022)).fv) :=
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

theorem support_mem_0024 :
    alpha_dummy_021 ∈
      (((syn_ccompl (Class.cv alpha_dummy_021))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_022))).fv) :=
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

theorem support_mem_0026 :
    alpha_dummy_021 ∈
      (((Class.cv alpha_dummy_021)).fv ∪ ((Class.cv alpha_dummy_021)).fv) :=
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

theorem support_mem_0028 :
    alpha_dummy_022 ∈
      (((syn_ccompl (Class.cv alpha_dummy_021))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_022))).fv) :=
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

theorem support_mem_0030 :
    alpha_dummy_022 ∈
      (((Class.cv alpha_dummy_022)).fv ∪ ((Class.cv alpha_dummy_022)).fv) :=
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

theorem support_mem_0032 :
    alpha_dummy_002 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0033 :
    alpha_dummy_002 ∈
      (((syn_ccompl (Class.cab alpha_dummy_006
              (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_001)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cphi (Class.cv alpha_dummy_007))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002)
                (Wff.classEq (Class.cv alpha_dummy_006)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_007))
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

theorem support_mem_0036 :
    alpha_dummy_002 ∈
      (((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_006 (syn_wrex alpha_dummy_007 (Class.cv alpha_dummy_002)
              (Wff.classEq (Class.cv alpha_dummy_006)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_007)) (syn_csn (syn_c0c))))))).fv) :=
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

theorem support_mem_0038 :
    alpha_dummy_007 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_007)))).fv ∪
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

theorem support_mem_0040 :
    alpha_dummy_007 ∈
      (((syn_cphi (Class.cv alpha_dummy_007))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_007))).fv) :=
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

theorem support_mem_0042 :
    alpha_dummy_003 ∈
      (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0043 :
    alpha_dummy_003 ∈
      (((syn_ccompl (Class.cab alpha_dummy_042
              (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_043))
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

theorem support_mem_0044 (z : Var) (w : Var) :
    z ∈ (((Class.cv z)).fv ∪ ((Class.cv w)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0045 (z : Var) (w : Var) :
    z ∈
      (((syn_ccompl (Class.cab (alpha_dummy_044 z w)
              (syn_wrex (alpha_dummy_045 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                  (syn_cphi (Class.cv (alpha_dummy_045 z w)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_045 z w)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0046 :
    alpha_dummy_003 ∈
      (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cphi (Class.cv alpha_dummy_043)))))).fv ∪ ((Class.cab alpha_dummy_042
            (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cphi (Class.cv alpha_dummy_043)))))).fv) :=
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

theorem support_mem_0047 (z : Var) (w : Var) :
    z ∈
      (((Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                (syn_cphi (Class.cv (alpha_dummy_045 z w))))))).fv ∪
        ((Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                (syn_cphi (Class.cv (alpha_dummy_045 z w))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0048 : alpha_dummy_043 ∈ (((Class.cv alpha_dummy_043)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0049 (z : Var) (w : Var) :
    (alpha_dummy_045 z w) ∈ (((Class.cv (alpha_dummy_045 z w))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0050 :
    alpha_dummy_050 ∈
      (((Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_050) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_050)).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0051 (z : Var) (w : Var) :
    (alpha_dummy_052 z w) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_052 z w)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_052 z w)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_052 z w))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0052 :
    alpha_dummy_050 ∈ (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0053 (z : Var) (w : Var) :
    (alpha_dummy_052 z w) ∈ (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0054 :
    alpha_dummy_057 ∈
      (((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0055 (z : Var) (w : Var) :
    (alpha_dummy_060 z w) ∈
      (((syn_cnin (Class.cv (alpha_dummy_060 z w)) (Class.cv (alpha_dummy_061 z w)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_060 z w)) (Class.cv (alpha_dummy_061 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0056 :
    alpha_dummy_057 ∈
      (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_058)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0057 (z : Var) (w : Var) :
    (alpha_dummy_060 z w) ∈
      (((Class.cv (alpha_dummy_060 z w))).fv ∪ ((Class.cv (alpha_dummy_061 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0058 :
    alpha_dummy_058 ∈
      (((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0059 (z : Var) (w : Var) :
    (alpha_dummy_061 z w) ∈
      (((syn_cnin (Class.cv (alpha_dummy_060 z w)) (Class.cv (alpha_dummy_061 z w)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_060 z w)) (Class.cv (alpha_dummy_061 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0060 :
    alpha_dummy_058 ∈
      (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_058)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0061 (z : Var) (w : Var) :
    (alpha_dummy_061 z w) ∈
      (((Class.cv (alpha_dummy_060 z w))).fv ∪ ((Class.cv (alpha_dummy_061 z w))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0062 :
    alpha_dummy_057 ∈
      (((syn_ccompl (Class.cv alpha_dummy_057))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_058))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0063 (z : Var) (w : Var) :
    (alpha_dummy_060 z w) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_060 z w)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_061 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0064 :
    alpha_dummy_057 ∈
      (((Class.cv alpha_dummy_057)).fv ∪ ((Class.cv alpha_dummy_057)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0065 (z : Var) (w : Var) :
    (alpha_dummy_060 z w) ∈
      (((Class.cv (alpha_dummy_060 z w))).fv ∪ ((Class.cv (alpha_dummy_060 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0066 :
    alpha_dummy_058 ∈
      (((syn_ccompl (Class.cv alpha_dummy_057))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_058))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0067 (z : Var) (w : Var) :
    (alpha_dummy_061 z w) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_060 z w)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_061 z w)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0068 :
    alpha_dummy_058 ∈
      (((Class.cv alpha_dummy_058)).fv ∪ ((Class.cv alpha_dummy_058)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0069 (z : Var) (w : Var) :
    (alpha_dummy_061 z w) ∈
      (((Class.cv (alpha_dummy_061 z w))).fv ∪ ((Class.cv (alpha_dummy_061 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0070 :
    alpha_dummy_000 ∈
      (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0071 :
    alpha_dummy_000 ∈
      (((syn_ccompl (Class.cab alpha_dummy_042
              (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cphi (Class.cv alpha_dummy_043))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_043))
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

theorem support_mem_0072 (z : Var) (w : Var) :
    w ∈ (((Class.cv z)).fv ∪ ((Class.cv w)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0073 (z : Var) (w : Var) :
    w ∈
      (((syn_ccompl (Class.cab (alpha_dummy_044 z w)
              (syn_wrex (alpha_dummy_045 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                  (syn_cphi (Class.cv (alpha_dummy_045 z w)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_045 z w)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0074 :
    alpha_dummy_000 ∈
      (((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_042 (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_042)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))).fv) :=
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

theorem support_mem_0075 (z : Var) (w : Var) :
    w ∈
      (((Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_045 z w)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_044 z w)
            (syn_wrex (alpha_dummy_045 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_045 z w)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0076 :
    alpha_dummy_043 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_043)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0077 (z : Var) (w : Var) :
    (alpha_dummy_045 z w) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_045 z w))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0078 :
    alpha_dummy_043 ∈
      (((syn_cphi (Class.cv alpha_dummy_043))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_043))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0079 (z : Var) (w : Var) :
    (alpha_dummy_045 z w) ∈
      (((syn_cphi (Class.cv (alpha_dummy_045 z w)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_045 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0080 :
    alpha_dummy_000 ∈
      (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0081 :
    alpha_dummy_000 ∈
      (((syn_ccompl (Class.cab alpha_dummy_078
              (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_078)
                  (syn_cphi (Class.cv alpha_dummy_079))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003)
                (Wff.classEq (Class.cv alpha_dummy_078)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_079))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0082 (z : Var) (w : Var) :
    w ∈ (((Class.cv w)).fv ∪ ((Class.cv z)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0083 (z : Var) (w : Var) :
    w ∈
      (((syn_ccompl (Class.cab (alpha_dummy_080 z w)
              (syn_wrex (alpha_dummy_081 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                  (syn_cphi (Class.cv (alpha_dummy_081 z w)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_081 z w)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0084 :
    alpha_dummy_000 ∈
      (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_078)
                (syn_cphi (Class.cv alpha_dummy_079)))))).fv ∪ ((Class.cab alpha_dummy_078
            (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000)
              (Wff.classEq (Class.cv alpha_dummy_078)
                (syn_cphi (Class.cv alpha_dummy_079)))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0085 (z : Var) (w : Var) :
    w ∈
      (((Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                (syn_cphi (Class.cv (alpha_dummy_081 z w))))))).fv ∪
        ((Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                (syn_cphi (Class.cv (alpha_dummy_081 z w))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0086 : alpha_dummy_079 ∈ (((Class.cv alpha_dummy_079)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0087 (z : Var) (w : Var) :
    (alpha_dummy_081 z w) ∈ (((Class.cv (alpha_dummy_081 z w))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0088 :
    alpha_dummy_086 ∈
      (((Wff.classMem (Class.cv alpha_dummy_086) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_086) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_086)).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0089 (z : Var) (w : Var) :
    (alpha_dummy_088 z w) ∈
      (((Wff.classMem (Class.cv (alpha_dummy_088 z w)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (alpha_dummy_088 z w)) (syn_c1c))).fv ∪
        ((Class.cv (alpha_dummy_088 z w))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0090 :
    alpha_dummy_086 ∈ (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0091 (z : Var) (w : Var) :
    (alpha_dummy_088 z w) ∈ (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0092 :
    alpha_dummy_093 ∈
      (((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0093 (z : Var) (w : Var) :
    (alpha_dummy_096 z w) ∈
      (((syn_cnin (Class.cv (alpha_dummy_096 z w)) (Class.cv (alpha_dummy_097 z w)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_096 z w)) (Class.cv (alpha_dummy_097 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0094 :
    alpha_dummy_093 ∈
      (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_094)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0095 (z : Var) (w : Var) :
    (alpha_dummy_096 z w) ∈
      (((Class.cv (alpha_dummy_096 z w))).fv ∪ ((Class.cv (alpha_dummy_097 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0096 :
    alpha_dummy_094 ∈
      (((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0097 (z : Var) (w : Var) :
    (alpha_dummy_097 z w) ∈
      (((syn_cnin (Class.cv (alpha_dummy_096 z w)) (Class.cv (alpha_dummy_097 z w)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_096 z w)) (Class.cv (alpha_dummy_097 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0098 :
    alpha_dummy_094 ∈
      (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_094)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0099 (z : Var) (w : Var) :
    (alpha_dummy_097 z w) ∈
      (((Class.cv (alpha_dummy_096 z w))).fv ∪ ((Class.cv (alpha_dummy_097 z w))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0100 :
    alpha_dummy_093 ∈
      (((syn_ccompl (Class.cv alpha_dummy_093))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_094))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0101 (z : Var) (w : Var) :
    (alpha_dummy_096 z w) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_096 z w)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_097 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0102 :
    alpha_dummy_093 ∈
      (((Class.cv alpha_dummy_093)).fv ∪ ((Class.cv alpha_dummy_093)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0103 (z : Var) (w : Var) :
    (alpha_dummy_096 z w) ∈
      (((Class.cv (alpha_dummy_096 z w))).fv ∪ ((Class.cv (alpha_dummy_096 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0104 :
    alpha_dummy_094 ∈
      (((syn_ccompl (Class.cv alpha_dummy_093))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_094))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0105 (z : Var) (w : Var) :
    (alpha_dummy_097 z w) ∈
      (((syn_ccompl (Class.cv (alpha_dummy_096 z w)))).fv ∪
        ((syn_ccompl (Class.cv (alpha_dummy_097 z w)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0106 :
    alpha_dummy_094 ∈
      (((Class.cv alpha_dummy_094)).fv ∪ ((Class.cv alpha_dummy_094)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0107 (z : Var) (w : Var) :
    (alpha_dummy_097 z w) ∈
      (((Class.cv (alpha_dummy_097 z w))).fv ∪ ((Class.cv (alpha_dummy_097 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0108 :
    alpha_dummy_003 ∈
      (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0109 :
    alpha_dummy_003 ∈
      (((syn_ccompl (Class.cab alpha_dummy_078
              (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_000)
                (Wff.classEq (Class.cv alpha_dummy_078)
                  (syn_cphi (Class.cv alpha_dummy_079))))))).fv ∪ ((syn_ccompl
            (Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003)
                (Wff.classEq (Class.cv alpha_dummy_078)
                  (syn_cun (syn_cphi (Class.cv alpha_dummy_079))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0110 (z : Var) (w : Var) :
    z ∈ (((Class.cv w)).fv ∪ ((Class.cv z)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0111 (z : Var) (w : Var) :
    z ∈
      (((syn_ccompl (Class.cab (alpha_dummy_080 z w)
              (syn_wrex (alpha_dummy_081 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                  (syn_cphi (Class.cv (alpha_dummy_081 z w)))))))).fv ∪ ((syn_ccompl
            (Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                  (syn_cun (syn_cphi (Class.cv (alpha_dummy_081 z w)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0112 :
    alpha_dummy_003 ∈
      (((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003)
              (Wff.classEq (Class.cv alpha_dummy_078)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab alpha_dummy_078 (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003)
              (Wff.classEq (Class.cv alpha_dummy_078)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0113 (z : Var) (w : Var) :
    z ∈
      (((Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_081 z w)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (alpha_dummy_080 z w)
            (syn_wrex (alpha_dummy_081 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_081 z w)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 0))
  · rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem support_mem_0114 :
    alpha_dummy_079 ∈
      (((syn_ccompl (syn_cphi (Class.cv alpha_dummy_079)))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0115 (z : Var) (w : Var) :
    (alpha_dummy_081 z w) ∈
      (((syn_ccompl (syn_cphi (Class.cv (alpha_dummy_081 z w))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0116 :
    alpha_dummy_079 ∈
      (((syn_cphi (Class.cv alpha_dummy_079))).fv ∪
        ((syn_cphi (Class.cv alpha_dummy_079))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0117 (z : Var) (w : Var) :
    (alpha_dummy_081 z w) ∈
      (((syn_cphi (Class.cv (alpha_dummy_081 z w)))).fv ∪
        ((syn_cphi (Class.cv (alpha_dummy_081 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end SwapAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
