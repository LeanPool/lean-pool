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

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_000`. -/
@[expose]
def alphaDummy000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_001`. -/
@[expose]
def alphaDummy001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_002`. -/
@[expose]
def alphaDummy002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_003`. -/
@[expose]
def alphaDummy003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_004`. -/
@[expose]
def alphaDummy004 : Var :=
  (freshVar (({ alphaDummy001 } : Finset Var) ∪ ({ alphaDummy002 } : Finset Var) ∪
      ((synWex alphaDummy003 (synWex alphaDummy000 (synWa
              (Wff.classEq (Class.cv alphaDummy001)
                (synCop (Class.cv alphaDummy003) (Class.cv alphaDummy000)))
              (Wff.classEq (Class.cv alphaDummy002)
                (synCop (Class.cv alphaDummy000) (Class.cv alphaDummy003))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_005`. -/
@[expose]
def alphaDummy005 (x : Var) (y : Var) (z : Var) (w : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z (synWex w
            (synWa (Wff.classEq (Class.cv x) (synCop (Class.cv z) (Class.cv w)))
              (Wff.classEq (Class.cv y) (synCop (Class.cv w) (Class.cv z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_006`. -/
@[expose]
def alphaDummy006 : Var :=
  (freshVar (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_007`. -/
@[expose]
def alphaDummy007 : Var :=
  (freshVar (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_008`. -/
@[expose]
def alphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_009`. -/
@[expose]
def alphaDummy009 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_010`. -/
@[expose]
def alphaDummy010 : Var :=
  (freshVar (((synCcompl (Class.cab alphaDummy006
            (synWrex alphaDummy007 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCphi (Class.cv alphaDummy007))))))).fv ∪ ((synCcompl
          (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy002)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_011`. -/
@[expose]
def alphaDummy011 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy008 x y)
            (synWrex (alphaDummy009 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy008 x y))
                (synCphi (Class.cv (alphaDummy009 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy008 x y))
                (synCun (synCphi (Class.cv (alphaDummy009 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_012`. -/
@[expose]
def alphaDummy012 : Var :=
  (freshVar (((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy001)
            (Wff.classEq (Class.cv alphaDummy006)
              (synCphi (Class.cv alphaDummy007)))))).fv ∪ ((Class.cab alphaDummy006
          (synWrex alphaDummy007 (Class.cv alphaDummy001)
            (Wff.classEq (Class.cv alphaDummy006)
              (synCphi (Class.cv alphaDummy007)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_013`. -/
@[expose]
def alphaDummy013 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alphaDummy008 x y))
              (synCphi (Class.cv (alphaDummy009 x y))))))).fv ∪
      ((Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alphaDummy008 x y))
              (synCphi (Class.cv (alphaDummy009 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_014`. -/
@[expose]
def alphaDummy014 : Var :=
  (freshVar (((Class.cv alphaDummy007)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_015`. -/
@[expose]
def alphaDummy015 : Var :=
  (freshVar (((Class.cv alphaDummy007)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_016`. -/
@[expose]
def alphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy009 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_017`. -/
@[expose]
def alphaDummy017 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy009 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_018`. -/
@[expose]
def alphaDummy018 : Var :=
  (freshVar (((Wff.classMem (Class.cv alphaDummy014) (synCnnc))).fv ∪
        ((synCplc (Class.cv alphaDummy014) (synC1c))).fv ∪ ((Class.cv alphaDummy014)).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_019`. -/
@[expose]
def alphaDummy019 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy016 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy016 x y)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy016 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_020`. -/
@[expose]
def alphaDummy020 : Var :=
  (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_021`. -/
@[expose]
def alphaDummy021 : Var :=
  (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_022`. -/
@[expose]
def alphaDummy022 : Var :=
  (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_023`. -/
@[expose]
def alphaDummy023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_024`. -/
@[expose]
def alphaDummy024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_025`. -/
@[expose]
def alphaDummy025 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_036`. -/
@[expose]
def alphaDummy036 : Var :=
  (freshVar (((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy002)
            (Wff.classEq (Class.cv alphaDummy006)
              (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c))))))).fv ∪
      ((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy002)
            (Wff.classEq (Class.cv alphaDummy006)
              (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_037`. -/
@[expose]
def alphaDummy037 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy008 x y))
              (synCun (synCphi (Class.cv (alphaDummy009 x y))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy008 x y))
              (synCun (synCphi (Class.cv (alphaDummy009 x y))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_038`. -/
@[expose]
def alphaDummy038 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv alphaDummy007)))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_039`. -/
@[expose]
def alphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy009 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_040`. -/
@[expose]
def alphaDummy040 : Var :=
  (freshVar (((synCphi (Class.cv alphaDummy007))).fv ∪
      ((synCphi (Class.cv alphaDummy007))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_041`. -/
@[expose]
def alphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy009 x y)))).fv ∪
      ((synCphi (Class.cv (alphaDummy009 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_042`. -/
@[expose]
def alphaDummy042 : Var :=
  (freshVar (((Class.cv alphaDummy003)).fv ∪ ((Class.cv alphaDummy000)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_043`. -/
@[expose]
def alphaDummy043 : Var :=
  (freshVar (((Class.cv alphaDummy003)).fv ∪ ((Class.cv alphaDummy000)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_044`. -/
@[expose]
def alphaDummy044 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_045`. -/
@[expose]
def alphaDummy045 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_046`. -/
@[expose]
def alphaDummy046 : Var :=
  (freshVar (((synCcompl (Class.cab alphaDummy042
            (synWrex alphaDummy043 (Class.cv alphaDummy003)
              (Wff.classEq (Class.cv alphaDummy042)
                (synCphi (Class.cv alphaDummy043))))))).fv ∪ ((synCcompl
          (Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy042)
                (synCun (synCphi (Class.cv alphaDummy043)) (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_047`. -/
@[expose]
def alphaDummy047 (z : Var) (w : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy044 z w)
            (synWrex (alphaDummy045 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy044 z w))
                (synCphi (Class.cv (alphaDummy045 z w)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy044 z w))
                (synCun (synCphi (Class.cv (alphaDummy045 z w)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_048`. -/
@[expose]
def alphaDummy048 : Var :=
  (freshVar (((Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy003)
            (Wff.classEq (Class.cv alphaDummy042)
              (synCphi (Class.cv alphaDummy043)))))).fv ∪ ((Class.cab alphaDummy042
          (synWrex alphaDummy043 (Class.cv alphaDummy003)
            (Wff.classEq (Class.cv alphaDummy042)
              (synCphi (Class.cv alphaDummy043)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_049`. -/
@[expose]
def alphaDummy049 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy044 z w))
              (synCphi (Class.cv (alphaDummy045 z w))))))).fv ∪
      ((Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy044 z w))
              (synCphi (Class.cv (alphaDummy045 z w))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_050`. -/
@[expose]
def alphaDummy050 : Var :=
  (freshVar (((Class.cv alphaDummy043)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_051`. -/
@[expose]
def alphaDummy051 : Var :=
  (freshVar (((Class.cv alphaDummy043)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_052`. -/
@[expose]
def alphaDummy052 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy045 z w))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_053`. -/
@[expose]
def alphaDummy053 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy045 z w))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_054`. -/
@[expose]
def alphaDummy054 : Var :=
  (freshVar (((Wff.classMem (Class.cv alphaDummy050) (synCnnc))).fv ∪
        ((synCplc (Class.cv alphaDummy050) (synC1c))).fv ∪ ((Class.cv alphaDummy050)).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_055`. -/
@[expose]
def alphaDummy055 (z : Var) (w : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy052 z w)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy052 z w)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy052 z w))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_056`. -/
@[expose]
def alphaDummy056 : Var :=
  (freshVar (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_057`. -/
@[expose]
def alphaDummy057 : Var :=
  (freshVar (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_058`. -/
@[expose]
def alphaDummy058 : Var :=
  (freshVar (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_059`. -/
@[expose]
def alphaDummy059 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_060`. -/
@[expose]
def alphaDummy060 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_061`. -/
@[expose]
def alphaDummy061 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_072`. -/
@[expose]
def alphaDummy072 : Var :=
  (freshVar (((Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy000)
            (Wff.classEq (Class.cv alphaDummy042)
              (synCun (synCphi (Class.cv alphaDummy043)) (synCsn (synC0c))))))).fv ∪
      ((Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy000)
            (Wff.classEq (Class.cv alphaDummy042)
              (synCun (synCphi (Class.cv alphaDummy043)) (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_073`. -/
@[expose]
def alphaDummy073 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alphaDummy044 z w))
              (synCun (synCphi (Class.cv (alphaDummy045 z w))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alphaDummy044 z w))
              (synCun (synCphi (Class.cv (alphaDummy045 z w))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_074`. -/
@[expose]
def alphaDummy074 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv alphaDummy043)))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_075`. -/
@[expose]
def alphaDummy075 (z : Var) (w : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy045 z w))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_076`. -/
@[expose]
def alphaDummy076 : Var :=
  (freshVar (((synCphi (Class.cv alphaDummy043))).fv ∪
      ((synCphi (Class.cv alphaDummy043))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_077`. -/
@[expose]
def alphaDummy077 (z : Var) (w : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy045 z w)))).fv ∪
      ((synCphi (Class.cv (alphaDummy045 z w)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_078`. -/
@[expose]
def alphaDummy078 : Var :=
  (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy003)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_079`. -/
@[expose]
def alphaDummy079 : Var :=
  (freshVar (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy003)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_080`. -/
@[expose]
def alphaDummy080 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv w)).fv ∪ ((Class.cv z)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_081`. -/
@[expose]
def alphaDummy081 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv w)).fv ∪ ((Class.cv z)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_082`. -/
@[expose]
def alphaDummy082 : Var :=
  (freshVar (((synCcompl (Class.cab alphaDummy078
            (synWrex alphaDummy079 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy078)
                (synCphi (Class.cv alphaDummy079))))))).fv ∪ ((synCcompl
          (Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy003)
              (Wff.classEq (Class.cv alphaDummy078)
                (synCun (synCphi (Class.cv alphaDummy079)) (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_083`. -/
@[expose]
def alphaDummy083 (z : Var) (w : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy080 z w)
            (synWrex (alphaDummy081 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy080 z w))
                (synCphi (Class.cv (alphaDummy081 z w)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy080 z w))
                (synCun (synCphi (Class.cv (alphaDummy081 z w)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_084`. -/
@[expose]
def alphaDummy084 : Var :=
  (freshVar (((Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy000)
            (Wff.classEq (Class.cv alphaDummy078)
              (synCphi (Class.cv alphaDummy079)))))).fv ∪ ((Class.cab alphaDummy078
          (synWrex alphaDummy079 (Class.cv alphaDummy000)
            (Wff.classEq (Class.cv alphaDummy078)
              (synCphi (Class.cv alphaDummy079)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_085`. -/
@[expose]
def alphaDummy085 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alphaDummy080 z w))
              (synCphi (Class.cv (alphaDummy081 z w))))))).fv ∪
      ((Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alphaDummy080 z w))
              (synCphi (Class.cv (alphaDummy081 z w))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_086`. -/
@[expose]
def alphaDummy086 : Var :=
  (freshVar (((Class.cv alphaDummy079)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_087`. -/
@[expose]
def alphaDummy087 : Var :=
  (freshVar (((Class.cv alphaDummy079)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_088`. -/
@[expose]
def alphaDummy088 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy081 z w))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_089`. -/
@[expose]
def alphaDummy089 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy081 z w))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_090`. -/
@[expose]
def alphaDummy090 : Var :=
  (freshVar (((Wff.classMem (Class.cv alphaDummy086) (synCnnc))).fv ∪
        ((synCplc (Class.cv alphaDummy086) (synC1c))).fv ∪ ((Class.cv alphaDummy086)).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_091`. -/
@[expose]
def alphaDummy091 (z : Var) (w : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy088 z w)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy088 z w)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy088 z w))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_092`. -/
@[expose]
def alphaDummy092 : Var :=
  (freshVar (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_093`. -/
@[expose]
def alphaDummy093 : Var :=
  (freshVar (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_094`. -/
@[expose]
def alphaDummy094 : Var :=
  (freshVar (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_095`. -/
@[expose]
def alphaDummy095 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_096`. -/
@[expose]
def alphaDummy096 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_097`. -/
@[expose]
def alphaDummy097 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_108`. -/
@[expose]
def alphaDummy108 : Var :=
  (freshVar (((Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy003)
            (Wff.classEq (Class.cv alphaDummy078)
              (synCun (synCphi (Class.cv alphaDummy079)) (synCsn (synC0c))))))).fv ∪
      ((Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy003)
            (Wff.classEq (Class.cv alphaDummy078)
              (synCun (synCphi (Class.cv alphaDummy079)) (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_109`. -/
@[expose]
def alphaDummy109 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy080 z w))
              (synCun (synCphi (Class.cv (alphaDummy081 z w))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy080 z w))
              (synCun (synCphi (Class.cv (alphaDummy081 z w))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_110`. -/
@[expose]
def alphaDummy110 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv alphaDummy079)))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_111`. -/
@[expose]
def alphaDummy111 (z : Var) (w : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy081 z w))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_112`. -/
@[expose]
def alphaDummy112 : Var :=
  (freshVar (((synCphi (Class.cv alphaDummy079))).fv ∪
      ((synCphi (Class.cv alphaDummy079))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_113`. -/
@[expose]
def alphaDummy113 (z : Var) (w : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy081 z w)))).fv ∪
      ((synCphi (Class.cv (alphaDummy081 z w)))).fv) 0)

theorem mem_pair_support_left (u v : Var) (support : Finset Var) :
    u ∈ ({ u } ∪ { v } ∪ support) :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))

theorem mem_pair_support_right (u v : Var) (support : Finset Var) :
    v ∈ ({ u } ∪ { v } ∪ support) :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem support_mem_0000 :
    alphaDummy001 ∈
      (({ alphaDummy001 } : Finset Var) ∪ ({ alphaDummy002 } : Finset Var) ∪
        ((synWex alphaDummy003 (synWex alphaDummy000 (synWa
                (Wff.classEq (Class.cv alphaDummy001)
                  (synCop (Class.cv alphaDummy003) (Class.cv alphaDummy000)))
                (Wff.classEq (Class.cv alphaDummy002) (synCop (Class.cv alphaDummy000)
                    (Class.cv alphaDummy003))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_left alphaDummy001 alphaDummy002
        ((synWex alphaDummy003 (synWex alphaDummy000 (synWa
                (Wff.classEq (Class.cv alphaDummy001)
                  (synCop (Class.cv alphaDummy003) (Class.cv alphaDummy000)))
                (Wff.classEq (Class.cv alphaDummy002)
                  (synCop (Class.cv alphaDummy000) (Class.cv alphaDummy003))))))).fv

theorem support_mem_0001 (x : Var) (y : Var) (z : Var) (w : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z (synWex w
              (synWa (Wff.classEq (Class.cv x) (synCop (Class.cv z) (Class.cv w)))
                (Wff.classEq (Class.cv y) (synCop (Class.cv w) (Class.cv z))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_left x y
        ((synWex z (synWex w
              (synWa (Wff.classEq (Class.cv x) (synCop (Class.cv z) (Class.cv w)))
                (Wff.classEq (Class.cv y) (synCop (Class.cv w) (Class.cv z))))))).fv

theorem support_mem_0002 :
    alphaDummy002 ∈
      (({ alphaDummy001 } : Finset Var) ∪ ({ alphaDummy002 } : Finset Var) ∪
        ((synWex alphaDummy003 (synWex alphaDummy000 (synWa
                (Wff.classEq (Class.cv alphaDummy001)
                  (synCop (Class.cv alphaDummy003) (Class.cv alphaDummy000)))
                (Wff.classEq (Class.cv alphaDummy002) (synCop (Class.cv alphaDummy000)
                    (Class.cv alphaDummy003))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_right alphaDummy001 alphaDummy002
        ((synWex alphaDummy003 (synWex alphaDummy000 (synWa
                (Wff.classEq (Class.cv alphaDummy001)
                  (synCop (Class.cv alphaDummy003) (Class.cv alphaDummy000)))
                (Wff.classEq (Class.cv alphaDummy002)
                  (synCop (Class.cv alphaDummy000) (Class.cv alphaDummy003))))))).fv

theorem support_mem_0003 (x : Var) (y : Var) (z : Var) (w : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z (synWex w
              (synWa (Wff.classEq (Class.cv x) (synCop (Class.cv z) (Class.cv w)))
                (Wff.classEq (Class.cv y) (synCop (Class.cv w) (Class.cv z))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_right x y
        ((synWex z (synWex w
              (synWa (Wff.classEq (Class.cv x) (synCop (Class.cv z) (Class.cv w)))
                (Wff.classEq (Class.cv y) (synCop (Class.cv w) (Class.cv z))))))).fv

theorem support_mem_0004 :
    alphaDummy001 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0005 :
    alphaDummy001 ∈
      (((synCcompl (Class.cab alphaDummy006
              (synWrex alphaDummy007 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCphi (Class.cv alphaDummy007))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy002)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCun (synCphi (Class.cv alphaDummy007))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy008 x y)
              (synWrex (alphaDummy009 x y) (Class.cv x)
                (Wff.classEq (Class.cv (alphaDummy008 x y))
                  (synCphi (Class.cv (alphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv y)
                (Wff.classEq (Class.cv (alphaDummy008 x y))
                  (synCun (synCphi (Class.cv (alphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
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
    alphaDummy001 ∈
      (((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCphi (Class.cv alphaDummy007)))))).fv ∪ ((Class.cab alphaDummy006
            (synWrex alphaDummy007 (Class.cv alphaDummy001)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCphi (Class.cv alphaDummy007)))))).fv) :=
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
      (((Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy008 x y))
                (synCphi (Class.cv (alphaDummy009 x y))))))).fv ∪
        ((Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy008 x y))
                (synCphi (Class.cv (alphaDummy009 x y))))))).fv) :=
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

theorem support_mem_0010 : alphaDummy007 ∈ (((Class.cv alphaDummy007)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0011 (x : Var) (y : Var) :
    (alphaDummy009 x y) ∈ (((Class.cv (alphaDummy009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0012 :
    alphaDummy014 ∈
      (((Wff.classMem (Class.cv alphaDummy014) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy014) (synC1c))).fv ∪
        ((Class.cv alphaDummy014)).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0013 (x : Var) (y : Var) :
    (alphaDummy016 x y) ∈
      (((Wff.classMem (Class.cv (alphaDummy016 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy016 x y)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy016 x y))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0014 :
    alphaDummy014 ∈ (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0015 (x : Var) (y : Var) :
    (alphaDummy016 x y) ∈ (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0016 :
    alphaDummy021 ∈
      (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv ∪
        ((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0017 (x : Var) (y : Var) :
    (alphaDummy024 x y) ∈
      (((synCnin (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y)))).fv ∪
        ((synCnin (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0018 :
    alphaDummy021 ∈
      (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy022)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0019 (x : Var) (y : Var) :
    (alphaDummy024 x y) ∈
      (((Class.cv (alphaDummy024 x y))).fv ∪ ((Class.cv (alphaDummy025 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0020 :
    alphaDummy022 ∈
      (((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv ∪
        ((synCnin (Class.cv alphaDummy021) (Class.cv alphaDummy022))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0021 (x : Var) (y : Var) :
    (alphaDummy025 x y) ∈
      (((synCnin (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y)))).fv ∪
        ((synCnin (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0022 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy022)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0023 (x : Var) (y : Var) :
    (alphaDummy025 x y) ∈
      (((Class.cv (alphaDummy024 x y))).fv ∪ ((Class.cv (alphaDummy025 x y))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0024 :
    alphaDummy021 ∈
      (((synCcompl (Class.cv alphaDummy021))).fv ∪
        ((synCcompl (Class.cv alphaDummy022))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0025 (x : Var) (y : Var) :
    (alphaDummy024 x y) ∈
      (((synCcompl (Class.cv (alphaDummy024 x y)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy025 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0026 :
    alphaDummy021 ∈
      (((Class.cv alphaDummy021)).fv ∪ ((Class.cv alphaDummy021)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0027 (x : Var) (y : Var) :
    (alphaDummy024 x y) ∈
      (((Class.cv (alphaDummy024 x y))).fv ∪ ((Class.cv (alphaDummy024 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0028 :
    alphaDummy022 ∈
      (((synCcompl (Class.cv alphaDummy021))).fv ∪
        ((synCcompl (Class.cv alphaDummy022))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0029 (x : Var) (y : Var) :
    (alphaDummy025 x y) ∈
      (((synCcompl (Class.cv (alphaDummy024 x y)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy025 x y)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0030 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy022)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0031 (x : Var) (y : Var) :
    (alphaDummy025 x y) ∈
      (((Class.cv (alphaDummy025 x y))).fv ∪ ((Class.cv (alphaDummy025 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0032 :
    alphaDummy002 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0033 :
    alphaDummy002 ∈
      (((synCcompl (Class.cab alphaDummy006
              (synWrex alphaDummy007 (Class.cv alphaDummy001)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCphi (Class.cv alphaDummy007))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy002)
                (Wff.classEq (Class.cv alphaDummy006)
                  (synCun (synCphi (Class.cv alphaDummy007))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy008 x y)
              (synWrex (alphaDummy009 x y) (Class.cv x)
                (Wff.classEq (Class.cv (alphaDummy008 x y))
                  (synCphi (Class.cv (alphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv y)
                (Wff.classEq (Class.cv (alphaDummy008 x y))
                  (synCun (synCphi (Class.cv (alphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
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
    alphaDummy002 ∈
      (((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy002)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy006 (synWrex alphaDummy007 (Class.cv alphaDummy002)
              (Wff.classEq (Class.cv alphaDummy006)
                (synCun (synCphi (Class.cv alphaDummy007)) (synCsn (synC0c))))))).fv) :=
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
      (((Class.cab (alphaDummy008 x y) (synWrex (alphaDummy009 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy008 x y))
                (synCun (synCphi (Class.cv (alphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy008 x y)
            (synWrex (alphaDummy009 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy008 x y))
                (synCun (synCphi (Class.cv (alphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
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
    alphaDummy007 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy007)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0039 (x : Var) (y : Var) :
    (alphaDummy009 x y) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0040 :
    alphaDummy007 ∈
      (((synCphi (Class.cv alphaDummy007))).fv ∪
        ((synCphi (Class.cv alphaDummy007))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0041 (x : Var) (y : Var) :
    (alphaDummy009 x y) ∈
      (((synCphi (Class.cv (alphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (alphaDummy009 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0042 :
    alphaDummy003 ∈
      (((Class.cv alphaDummy003)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0043 :
    alphaDummy003 ∈
      (((synCcompl (Class.cab alphaDummy042
              (synWrex alphaDummy043 (Class.cv alphaDummy003)
                (Wff.classEq (Class.cv alphaDummy042)
                  (synCphi (Class.cv alphaDummy043))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy042)
                  (synCun (synCphi (Class.cv alphaDummy043))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy044 z w)
              (synWrex (alphaDummy045 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy044 z w))
                  (synCphi (Class.cv (alphaDummy045 z w)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alphaDummy044 z w))
                  (synCun (synCphi (Class.cv (alphaDummy045 z w)))
                    (synCsn (synC0c)))))))).fv) :=
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
    alphaDummy003 ∈
      (((Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy003)
              (Wff.classEq (Class.cv alphaDummy042)
                (synCphi (Class.cv alphaDummy043)))))).fv ∪ ((Class.cab alphaDummy042
            (synWrex alphaDummy043 (Class.cv alphaDummy003)
              (Wff.classEq (Class.cv alphaDummy042)
                (synCphi (Class.cv alphaDummy043)))))).fv) :=
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
      (((Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy044 z w))
                (synCphi (Class.cv (alphaDummy045 z w))))))).fv ∪
        ((Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy044 z w))
                (synCphi (Class.cv (alphaDummy045 z w))))))).fv) :=
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

theorem support_mem_0048 : alphaDummy043 ∈ (((Class.cv alphaDummy043)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0049 (z : Var) (w : Var) :
    (alphaDummy045 z w) ∈ (((Class.cv (alphaDummy045 z w))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0050 :
    alphaDummy050 ∈
      (((Wff.classMem (Class.cv alphaDummy050) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy050) (synC1c))).fv ∪
        ((Class.cv alphaDummy050)).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0051 (z : Var) (w : Var) :
    (alphaDummy052 z w) ∈
      (((Wff.classMem (Class.cv (alphaDummy052 z w)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy052 z w)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy052 z w))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0052 :
    alphaDummy050 ∈ (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0053 (z : Var) (w : Var) :
    (alphaDummy052 z w) ∈ (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0054 :
    alphaDummy057 ∈
      (((synCnin (Class.cv alphaDummy057) (Class.cv alphaDummy058))).fv ∪
        ((synCnin (Class.cv alphaDummy057) (Class.cv alphaDummy058))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0055 (z : Var) (w : Var) :
    (alphaDummy060 z w) ∈
      (((synCnin (Class.cv (alphaDummy060 z w)) (Class.cv (alphaDummy061 z w)))).fv ∪
        ((synCnin (Class.cv (alphaDummy060 z w)) (Class.cv (alphaDummy061 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0056 :
    alphaDummy057 ∈
      (((Class.cv alphaDummy057)).fv ∪ ((Class.cv alphaDummy058)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0057 (z : Var) (w : Var) :
    (alphaDummy060 z w) ∈
      (((Class.cv (alphaDummy060 z w))).fv ∪ ((Class.cv (alphaDummy061 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0058 :
    alphaDummy058 ∈
      (((synCnin (Class.cv alphaDummy057) (Class.cv alphaDummy058))).fv ∪
        ((synCnin (Class.cv alphaDummy057) (Class.cv alphaDummy058))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0059 (z : Var) (w : Var) :
    (alphaDummy061 z w) ∈
      (((synCnin (Class.cv (alphaDummy060 z w)) (Class.cv (alphaDummy061 z w)))).fv ∪
        ((synCnin (Class.cv (alphaDummy060 z w)) (Class.cv (alphaDummy061 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0060 :
    alphaDummy058 ∈
      (((Class.cv alphaDummy057)).fv ∪ ((Class.cv alphaDummy058)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0061 (z : Var) (w : Var) :
    (alphaDummy061 z w) ∈
      (((Class.cv (alphaDummy060 z w))).fv ∪ ((Class.cv (alphaDummy061 z w))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0062 :
    alphaDummy057 ∈
      (((synCcompl (Class.cv alphaDummy057))).fv ∪
        ((synCcompl (Class.cv alphaDummy058))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0063 (z : Var) (w : Var) :
    (alphaDummy060 z w) ∈
      (((synCcompl (Class.cv (alphaDummy060 z w)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy061 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0064 :
    alphaDummy057 ∈
      (((Class.cv alphaDummy057)).fv ∪ ((Class.cv alphaDummy057)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0065 (z : Var) (w : Var) :
    (alphaDummy060 z w) ∈
      (((Class.cv (alphaDummy060 z w))).fv ∪ ((Class.cv (alphaDummy060 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0066 :
    alphaDummy058 ∈
      (((synCcompl (Class.cv alphaDummy057))).fv ∪
        ((synCcompl (Class.cv alphaDummy058))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0067 (z : Var) (w : Var) :
    (alphaDummy061 z w) ∈
      (((synCcompl (Class.cv (alphaDummy060 z w)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy061 z w)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0068 :
    alphaDummy058 ∈
      (((Class.cv alphaDummy058)).fv ∪ ((Class.cv alphaDummy058)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0069 (z : Var) (w : Var) :
    (alphaDummy061 z w) ∈
      (((Class.cv (alphaDummy061 z w))).fv ∪ ((Class.cv (alphaDummy061 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0070 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy003)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0071 :
    alphaDummy000 ∈
      (((synCcompl (Class.cab alphaDummy042
              (synWrex alphaDummy043 (Class.cv alphaDummy003)
                (Wff.classEq (Class.cv alphaDummy042)
                  (synCphi (Class.cv alphaDummy043))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy042)
                  (synCun (synCphi (Class.cv alphaDummy043))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy044 z w)
              (synWrex (alphaDummy045 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy044 z w))
                  (synCphi (Class.cv (alphaDummy045 z w)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alphaDummy044 z w))
                  (synCun (synCphi (Class.cv (alphaDummy045 z w)))
                    (synCsn (synC0c)))))))).fv) :=
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
    alphaDummy000 ∈
      (((Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy042)
                (synCun (synCphi (Class.cv alphaDummy043)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy042 (synWrex alphaDummy043 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy042)
                (synCun (synCphi (Class.cv alphaDummy043)) (synCsn (synC0c))))))).fv) :=
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
      (((Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy044 z w))
                (synCun (synCphi (Class.cv (alphaDummy045 z w)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy044 z w)
            (synWrex (alphaDummy045 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy044 z w))
                (synCun (synCphi (Class.cv (alphaDummy045 z w)))
                  (synCsn (synC0c))))))).fv) :=
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
    alphaDummy043 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy043)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0077 (z : Var) (w : Var) :
    (alphaDummy045 z w) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy045 z w))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0078 :
    alphaDummy043 ∈
      (((synCphi (Class.cv alphaDummy043))).fv ∪
        ((synCphi (Class.cv alphaDummy043))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0079 (z : Var) (w : Var) :
    (alphaDummy045 z w) ∈
      (((synCphi (Class.cv (alphaDummy045 z w)))).fv ∪
        ((synCphi (Class.cv (alphaDummy045 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0080 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy003)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0081 :
    alphaDummy000 ∈
      (((synCcompl (Class.cab alphaDummy078
              (synWrex alphaDummy079 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy078)
                  (synCphi (Class.cv alphaDummy079))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy003)
                (Wff.classEq (Class.cv alphaDummy078)
                  (synCun (synCphi (Class.cv alphaDummy079))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy080 z w)
              (synWrex (alphaDummy081 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alphaDummy080 z w))
                  (synCphi (Class.cv (alphaDummy081 z w)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy080 z w))
                  (synCun (synCphi (Class.cv (alphaDummy081 z w)))
                    (synCsn (synC0c)))))))).fv) :=
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
    alphaDummy000 ∈
      (((Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy078)
                (synCphi (Class.cv alphaDummy079)))))).fv ∪ ((Class.cab alphaDummy078
            (synWrex alphaDummy079 (Class.cv alphaDummy000)
              (Wff.classEq (Class.cv alphaDummy078)
                (synCphi (Class.cv alphaDummy079)))))).fv) :=
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
      (((Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy080 z w))
                (synCphi (Class.cv (alphaDummy081 z w))))))).fv ∪
        ((Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy080 z w))
                (synCphi (Class.cv (alphaDummy081 z w))))))).fv) :=
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

theorem support_mem_0086 : alphaDummy079 ∈ (((Class.cv alphaDummy079)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0087 (z : Var) (w : Var) :
    (alphaDummy081 z w) ∈ (((Class.cv (alphaDummy081 z w))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0088 :
    alphaDummy086 ∈
      (((Wff.classMem (Class.cv alphaDummy086) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy086) (synC1c))).fv ∪
        ((Class.cv alphaDummy086)).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0089 (z : Var) (w : Var) :
    (alphaDummy088 z w) ∈
      (((Wff.classMem (Class.cv (alphaDummy088 z w)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy088 z w)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy088 z w))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0090 :
    alphaDummy086 ∈ (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0091 (z : Var) (w : Var) :
    (alphaDummy088 z w) ∈ (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0092 :
    alphaDummy093 ∈
      (((synCnin (Class.cv alphaDummy093) (Class.cv alphaDummy094))).fv ∪
        ((synCnin (Class.cv alphaDummy093) (Class.cv alphaDummy094))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0093 (z : Var) (w : Var) :
    (alphaDummy096 z w) ∈
      (((synCnin (Class.cv (alphaDummy096 z w)) (Class.cv (alphaDummy097 z w)))).fv ∪
        ((synCnin (Class.cv (alphaDummy096 z w)) (Class.cv (alphaDummy097 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0094 :
    alphaDummy093 ∈
      (((Class.cv alphaDummy093)).fv ∪ ((Class.cv alphaDummy094)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0095 (z : Var) (w : Var) :
    (alphaDummy096 z w) ∈
      (((Class.cv (alphaDummy096 z w))).fv ∪ ((Class.cv (alphaDummy097 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0096 :
    alphaDummy094 ∈
      (((synCnin (Class.cv alphaDummy093) (Class.cv alphaDummy094))).fv ∪
        ((synCnin (Class.cv alphaDummy093) (Class.cv alphaDummy094))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0097 (z : Var) (w : Var) :
    (alphaDummy097 z w) ∈
      (((synCnin (Class.cv (alphaDummy096 z w)) (Class.cv (alphaDummy097 z w)))).fv ∪
        ((synCnin (Class.cv (alphaDummy096 z w)) (Class.cv (alphaDummy097 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0098 :
    alphaDummy094 ∈
      (((Class.cv alphaDummy093)).fv ∪ ((Class.cv alphaDummy094)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0099 (z : Var) (w : Var) :
    (alphaDummy097 z w) ∈
      (((Class.cv (alphaDummy096 z w))).fv ∪ ((Class.cv (alphaDummy097 z w))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0100 :
    alphaDummy093 ∈
      (((synCcompl (Class.cv alphaDummy093))).fv ∪
        ((synCcompl (Class.cv alphaDummy094))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0101 (z : Var) (w : Var) :
    (alphaDummy096 z w) ∈
      (((synCcompl (Class.cv (alphaDummy096 z w)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy097 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0102 :
    alphaDummy093 ∈
      (((Class.cv alphaDummy093)).fv ∪ ((Class.cv alphaDummy093)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0103 (z : Var) (w : Var) :
    (alphaDummy096 z w) ∈
      (((Class.cv (alphaDummy096 z w))).fv ∪ ((Class.cv (alphaDummy096 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0104 :
    alphaDummy094 ∈
      (((synCcompl (Class.cv alphaDummy093))).fv ∪
        ((synCcompl (Class.cv alphaDummy094))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0105 (z : Var) (w : Var) :
    (alphaDummy097 z w) ∈
      (((synCcompl (Class.cv (alphaDummy096 z w)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy097 z w)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0106 :
    alphaDummy094 ∈
      (((Class.cv alphaDummy094)).fv ∪ ((Class.cv alphaDummy094)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0107 (z : Var) (w : Var) :
    (alphaDummy097 z w) ∈
      (((Class.cv (alphaDummy097 z w))).fv ∪ ((Class.cv (alphaDummy097 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0108 :
    alphaDummy003 ∈
      (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy003)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0109 :
    alphaDummy003 ∈
      (((synCcompl (Class.cab alphaDummy078
              (synWrex alphaDummy079 (Class.cv alphaDummy000)
                (Wff.classEq (Class.cv alphaDummy078)
                  (synCphi (Class.cv alphaDummy079))))))).fv ∪ ((synCcompl
            (Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy003)
                (Wff.classEq (Class.cv alphaDummy078)
                  (synCun (synCphi (Class.cv alphaDummy079))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy080 z w)
              (synWrex (alphaDummy081 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alphaDummy080 z w))
                  (synCphi (Class.cv (alphaDummy081 z w)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy080 z w))
                  (synCun (synCphi (Class.cv (alphaDummy081 z w)))
                    (synCsn (synC0c)))))))).fv) :=
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
    alphaDummy003 ∈
      (((Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy003)
              (Wff.classEq (Class.cv alphaDummy078)
                (synCun (synCphi (Class.cv alphaDummy079)) (synCsn (synC0c))))))).fv ∪
        ((Class.cab alphaDummy078 (synWrex alphaDummy079 (Class.cv alphaDummy003)
              (Wff.classEq (Class.cv alphaDummy078)
                (synCun (synCphi (Class.cv alphaDummy079)) (synCsn (synC0c))))))).fv) :=
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
      (((Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy080 z w))
                (synCun (synCphi (Class.cv (alphaDummy081 z w)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy080 z w)
            (synWrex (alphaDummy081 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy080 z w))
                (synCun (synCphi (Class.cv (alphaDummy081 z w)))
                  (synCsn (synC0c))))))).fv) :=
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
    alphaDummy079 ∈
      (((synCcompl (synCphi (Class.cv alphaDummy079)))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0115 (z : Var) (w : Var) :
    (alphaDummy081 z w) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy081 z w))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0116 :
    alphaDummy079 ∈
      (((synCphi (Class.cv alphaDummy079))).fv ∪
        ((synCphi (Class.cv alphaDummy079))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0117 (z : Var) (w : Var) :
    (alphaDummy081 z w) ∈
      (((synCphi (Class.cv (alphaDummy081 z w)))).fv ∪
        ((synCphi (Class.cv (alphaDummy081 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end SwapAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
