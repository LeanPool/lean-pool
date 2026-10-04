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

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_000`. -/
@[expose]
def alphaDummy000 (A : Class) (B : Class) : Var :=
  (freshVar ((A).fv ∪ (B).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_001`. -/
@[expose]
def alphaDummy001 (A : Class) (B : Class) : Var :=
  (freshVar ((A).fv ∪ (B).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_002`. -/
@[expose]
def alphaDummy002 (A : Class) (B : Class) : Var :=
  (freshVar ((A).fv ∪ (B).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_003`. -/
@[expose]
def alphaDummy003 (A : Class) (B : Class) : Var :=
  (freshVar (({(alphaDummy000 A B)} : Finset Var) ∪ ({(alphaDummy001 A B)} : Finset Var) ∪
      ((synWex (alphaDummy002 A B) (synWa
            (synWbr (Class.cv (alphaDummy000 A B)) B (Class.cv (alphaDummy002 A B)))
            (synWbr (Class.cv (alphaDummy002 A B)) A (Class.cv (alphaDummy001 A B)))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_004`. -/
@[expose]
def alphaDummy004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z
          (synWa (synWbr (Class.cv x) B (Class.cv z))
            (synWbr (Class.cv z) A (Class.cv y))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_005`. -/
@[expose]
def alphaDummy005 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_006`. -/
@[expose]
def alphaDummy006 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_007`. -/
@[expose]
def alphaDummy007 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_008`. -/
@[expose]
def alphaDummy008 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_009`. -/
@[expose]
def alphaDummy009 (A : Class) (B : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy005 A B)
            (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy000 A B))
              (Wff.classEq (Class.cv (alphaDummy005 A B))
                (synCphi (Class.cv (alphaDummy006 A B)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy005 A B)
            (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy001 A B))
              (Wff.classEq (Class.cv (alphaDummy005 A B))
                (synCun (synCphi (Class.cv (alphaDummy006 A B)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_010`. -/
@[expose]
def alphaDummy010 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy007 x y)
            (synWrex (alphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy007 x y))
                (synCphi (Class.cv (alphaDummy008 x y)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy007 x y))
                (synCun (synCphi (Class.cv (alphaDummy008 x y)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_011`. -/
@[expose]
def alphaDummy011 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy005 A B)
          (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy000 A B))
            (Wff.classEq (Class.cv (alphaDummy005 A B))
              (synCphi (Class.cv (alphaDummy006 A B))))))).fv ∪
      ((Class.cab (alphaDummy005 A B)
          (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy000 A B))
            (Wff.classEq (Class.cv (alphaDummy005 A B))
              (synCphi (Class.cv (alphaDummy006 A B))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_012`. -/
@[expose]
def alphaDummy012 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alphaDummy007 x y))
              (synCphi (Class.cv (alphaDummy008 x y))))))).fv ∪
      ((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv x)
            (Wff.classEq (Class.cv (alphaDummy007 x y))
              (synCphi (Class.cv (alphaDummy008 x y))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_013`. -/
@[expose]
def alphaDummy013 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy006 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_014`. -/
@[expose]
def alphaDummy014 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy006 A B))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_015`. -/
@[expose]
def alphaDummy015 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy008 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_016`. -/
@[expose]
def alphaDummy016 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy008 x y))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_017`. -/
@[expose]
def alphaDummy017 (A : Class) (B : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy013 A B)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy013 A B)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy013 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_018`. -/
@[expose]
def alphaDummy018 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy015 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy015 x y)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy015 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_019`. -/
@[expose]
def alphaDummy019 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_020`. -/
@[expose]
def alphaDummy020 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_021`. -/
@[expose]
def alphaDummy021 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_022`. -/
@[expose]
def alphaDummy022 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_023`. -/
@[expose]
def alphaDummy023 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_024`. -/
@[expose]
def alphaDummy024 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_035`. -/
@[expose]
def alphaDummy035 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy005 A B)
          (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy001 A B))
            (Wff.classEq (Class.cv (alphaDummy005 A B))
              (synCun (synCphi (Class.cv (alphaDummy006 A B))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy005 A B)
          (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy001 A B))
            (Wff.classEq (Class.cv (alphaDummy005 A B))
              (synCun (synCphi (Class.cv (alphaDummy006 A B))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_036`. -/
@[expose]
def alphaDummy036 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy007 x y))
              (synCun (synCphi (Class.cv (alphaDummy008 x y))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy007 x y))
              (synCun (synCphi (Class.cv (alphaDummy008 x y))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_037`. -/
@[expose]
def alphaDummy037 (A : Class) (B : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy006 A B))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_038`. -/
@[expose]
def alphaDummy038 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy008 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_039`. -/
@[expose]
def alphaDummy039 (A : Class) (B : Class) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy006 A B)))).fv ∪
      ((synCphi (Class.cv (alphaDummy006 A B)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_040`. -/
@[expose]
def alphaDummy040 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy008 x y)))).fv ∪
      ((synCphi (Class.cv (alphaDummy008 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_041`. -/
@[expose]
def alphaDummy041 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy002 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_042`. -/
@[expose]
def alphaDummy042 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy002 A B))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_043`. -/
@[expose]
def alphaDummy043 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_044`. -/
@[expose]
def alphaDummy044 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_045`. -/
@[expose]
def alphaDummy045 (A : Class) (B : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy041 A B)
            (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy000 A B))
              (Wff.classEq (Class.cv (alphaDummy041 A B))
                (synCphi (Class.cv (alphaDummy042 A B)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy041 A B)
            (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy002 A B))
              (Wff.classEq (Class.cv (alphaDummy041 A B))
                (synCun (synCphi (Class.cv (alphaDummy042 A B)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_046`. -/
@[expose]
def alphaDummy046 (x : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy043 x z)
            (synWrex (alphaDummy044 x z) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy043 x z))
                (synCphi (Class.cv (alphaDummy044 x z)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy043 x z))
                (synCun (synCphi (Class.cv (alphaDummy044 x z)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_047`. -/
@[expose]
def alphaDummy047 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy041 A B)
          (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy000 A B))
            (Wff.classEq (Class.cv (alphaDummy041 A B))
              (synCphi (Class.cv (alphaDummy042 A B))))))).fv ∪
      ((Class.cab (alphaDummy041 A B)
          (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy000 A B))
            (Wff.classEq (Class.cv (alphaDummy041 A B))
              (synCphi (Class.cv (alphaDummy042 A B))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_048`. -/
@[expose]
def alphaDummy048 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv x)
            (Wff.classEq (Class.cv (alphaDummy043 x z))
              (synCphi (Class.cv (alphaDummy044 x z))))))).fv ∪
      ((Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv x)
            (Wff.classEq (Class.cv (alphaDummy043 x z))
              (synCphi (Class.cv (alphaDummy044 x z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_049`. -/
@[expose]
def alphaDummy049 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy042 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_050`. -/
@[expose]
def alphaDummy050 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy042 A B))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_051`. -/
@[expose]
def alphaDummy051 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy044 x z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_052`. -/
@[expose]
def alphaDummy052 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy044 x z))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_053`. -/
@[expose]
def alphaDummy053 (A : Class) (B : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy049 A B)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy049 A B)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy049 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_054`. -/
@[expose]
def alphaDummy054 (x : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy051 x z)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy051 x z)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy051 x z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_055`. -/
@[expose]
def alphaDummy055 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_056`. -/
@[expose]
def alphaDummy056 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_057`. -/
@[expose]
def alphaDummy057 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_058`. -/
@[expose]
def alphaDummy058 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_059`. -/
@[expose]
def alphaDummy059 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_060`. -/
@[expose]
def alphaDummy060 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_071`. -/
@[expose]
def alphaDummy071 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy041 A B)
          (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy002 A B))
            (Wff.classEq (Class.cv (alphaDummy041 A B))
              (synCun (synCphi (Class.cv (alphaDummy042 A B))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy041 A B)
          (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy002 A B))
            (Wff.classEq (Class.cv (alphaDummy041 A B))
              (synCun (synCphi (Class.cv (alphaDummy042 A B))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_072`. -/
@[expose]
def alphaDummy072 (x : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy043 x z))
              (synCun (synCphi (Class.cv (alphaDummy044 x z))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy043 x z))
              (synCun (synCphi (Class.cv (alphaDummy044 x z))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_073`. -/
@[expose]
def alphaDummy073 (A : Class) (B : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy042 A B))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_074`. -/
@[expose]
def alphaDummy074 (x : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy044 x z))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_075`. -/
@[expose]
def alphaDummy075 (A : Class) (B : Class) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy042 A B)))).fv ∪
      ((synCphi (Class.cv (alphaDummy042 A B)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_076`. -/
@[expose]
def alphaDummy076 (x : Var) (z : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy044 x z)))).fv ∪
      ((synCphi (Class.cv (alphaDummy044 x z)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_077`. -/
@[expose]
def alphaDummy077 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy002 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_078`. -/
@[expose]
def alphaDummy078 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy002 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_079`. -/
@[expose]
def alphaDummy079 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_080`. -/
@[expose]
def alphaDummy080 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv y)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_081`. -/
@[expose]
def alphaDummy081 (A : Class) (B : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy077 A B)
            (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy002 A B))
              (Wff.classEq (Class.cv (alphaDummy077 A B))
                (synCphi (Class.cv (alphaDummy078 A B)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy077 A B)
            (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy001 A B))
              (Wff.classEq (Class.cv (alphaDummy077 A B))
                (synCun (synCphi (Class.cv (alphaDummy078 A B)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_082`. -/
@[expose]
def alphaDummy082 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy079 y z)
            (synWrex (alphaDummy080 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy079 y z))
                (synCphi (Class.cv (alphaDummy080 y z)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy079 y z))
                (synCun (synCphi (Class.cv (alphaDummy080 y z)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_083`. -/
@[expose]
def alphaDummy083 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy077 A B)
          (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy002 A B))
            (Wff.classEq (Class.cv (alphaDummy077 A B))
              (synCphi (Class.cv (alphaDummy078 A B))))))).fv ∪
      ((Class.cab (alphaDummy077 A B)
          (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy002 A B))
            (Wff.classEq (Class.cv (alphaDummy077 A B))
              (synCphi (Class.cv (alphaDummy078 A B))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_084`. -/
@[expose]
def alphaDummy084 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy079 y z))
              (synCphi (Class.cv (alphaDummy080 y z))))))).fv ∪
      ((Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy079 y z))
              (synCphi (Class.cv (alphaDummy080 y z))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_085`. -/
@[expose]
def alphaDummy085 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy078 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_086`. -/
@[expose]
def alphaDummy086 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy078 A B))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_087`. -/
@[expose]
def alphaDummy087 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy080 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_088`. -/
@[expose]
def alphaDummy088 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy080 y z))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_089`. -/
@[expose]
def alphaDummy089 (A : Class) (B : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy085 A B)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy085 A B)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy085 A B))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_090`. -/
@[expose]
def alphaDummy090 (y : Var) (z : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy087 y z)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy087 y z)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy087 y z))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_091`. -/
@[expose]
def alphaDummy091 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_092`. -/
@[expose]
def alphaDummy092 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_093`. -/
@[expose]
def alphaDummy093 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_094`. -/
@[expose]
def alphaDummy094 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_095`. -/
@[expose]
def alphaDummy095 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_096`. -/
@[expose]
def alphaDummy096 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_107`. -/
@[expose]
def alphaDummy107 (A : Class) (B : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy077 A B)
          (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy001 A B))
            (Wff.classEq (Class.cv (alphaDummy077 A B))
              (synCun (synCphi (Class.cv (alphaDummy078 A B))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy077 A B)
          (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy001 A B))
            (Wff.classEq (Class.cv (alphaDummy077 A B))
              (synCun (synCphi (Class.cv (alphaDummy078 A B))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_108`. -/
@[expose]
def alphaDummy108 (y : Var) (z : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy079 y z))
              (synCun (synCphi (Class.cv (alphaDummy080 y z))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy079 y z))
              (synCun (synCphi (Class.cv (alphaDummy080 y z))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_109`. -/
@[expose]
def alphaDummy109 (A : Class) (B : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy078 A B))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_110`. -/
@[expose]
def alphaDummy110 (y : Var) (z : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy080 y z))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_111`. -/
@[expose]
def alphaDummy111 (A : Class) (B : Class) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy078 A B)))).fv ∪
      ((synCphi (Class.cv (alphaDummy078 A B)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_112`. -/
@[expose]
def alphaDummy112 (y : Var) (z : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy080 y z)))).fv ∪
      ((synCphi (Class.cv (alphaDummy080 y z)))).fv) 0)

theorem support_mem_0000 (A : Class) (B : Class) :
    (alphaDummy000 A B) ∈
      (({(alphaDummy000 A B)} : Finset Var) ∪ ({(alphaDummy001 A B)} : Finset Var) ∪
        ((synWex (alphaDummy002 A B) (synWa (synWbr (Class.cv (alphaDummy000 A B)) B
                (Class.cv (alphaDummy002 A B))) (synWbr (Class.cv (alphaDummy002 A B)) A
                (Class.cv (alphaDummy001 A B)))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem support_mem_0001 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z
            (synWa (synWbr (Class.cv x) B (Class.cv z))
              (synWbr (Class.cv z) A (Class.cv y))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem support_mem_0002 (A : Class) (B : Class) :
    (alphaDummy001 A B) ∈
      (({(alphaDummy000 A B)} : Finset Var) ∪ ({(alphaDummy001 A B)} : Finset Var) ∪
        ((synWex (alphaDummy002 A B) (synWa (synWbr (Class.cv (alphaDummy000 A B)) B
                (Class.cv (alphaDummy002 A B))) (synWbr (Class.cv (alphaDummy002 A B)) A
                (Class.cv (alphaDummy001 A B)))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem support_mem_0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z
            (synWa (synWbr (Class.cv x) B (Class.cv z))
              (synWbr (Class.cv z) A (Class.cv y))))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem support_mem_0004 (A : Class) (B : Class) :
    (alphaDummy000 A B) ∈
      (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0005 (A : Class) (B : Class) :
    (alphaDummy000 A B) ∈
      (((synCcompl (Class.cab (alphaDummy005 A B)
              (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy000 A B))
                (Wff.classEq (Class.cv (alphaDummy005 A B))
                  (synCphi (Class.cv (alphaDummy006 A B)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy005 A B)
              (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy001 A B))
                (Wff.classEq (Class.cv (alphaDummy005 A B))
                  (synCun (synCphi (Class.cv (alphaDummy006 A B)))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy007 x y)
              (synWrex (alphaDummy008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (alphaDummy007 x y))
                  (synCphi (Class.cv (alphaDummy008 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (alphaDummy007 x y))
                  (synCun (synCphi (Class.cv (alphaDummy008 x y)))
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

theorem support_mem_0008 (A : Class) (B : Class) :
    (alphaDummy000 A B) ∈
      (((Class.cab (alphaDummy005 A B)
            (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy000 A B))
              (Wff.classEq (Class.cv (alphaDummy005 A B))
                (synCphi (Class.cv (alphaDummy006 A B))))))).fv ∪
        ((Class.cab (alphaDummy005 A B)
            (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy000 A B))
              (Wff.classEq (Class.cv (alphaDummy005 A B))
                (synCphi (Class.cv (alphaDummy006 A B))))))).fv) :=
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
      (((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy007 x y))
                (synCphi (Class.cv (alphaDummy008 x y))))))).fv ∪
        ((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy007 x y))
                (synCphi (Class.cv (alphaDummy008 x y))))))).fv) :=
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
    (alphaDummy006 A B) ∈ (((Class.cv (alphaDummy006 A B))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0011 (x : Var) (y : Var) :
    (alphaDummy008 x y) ∈ (((Class.cv (alphaDummy008 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0012 (A : Class) (B : Class) :
    (alphaDummy013 A B) ∈
      (((Wff.classMem (Class.cv (alphaDummy013 A B)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy013 A B)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy013 A B))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0013 (x : Var) (y : Var) :
    (alphaDummy015 x y) ∈
      (((Wff.classMem (Class.cv (alphaDummy015 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy015 x y)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy015 x y))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0014 (A : Class) (B : Class) :
    (alphaDummy013 A B) ∈ (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0015 (x : Var) (y : Var) :
    (alphaDummy015 x y) ∈ (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0016 (A : Class) (B : Class) :
    (alphaDummy020 A B) ∈
      (((synCnin (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B)))).fv ∪
        ((synCnin (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0017 (x : Var) (y : Var) :
    (alphaDummy023 x y) ∈
      (((synCnin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))).fv ∪
        ((synCnin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0018 (A : Class) (B : Class) :
    (alphaDummy020 A B) ∈
      (((Class.cv (alphaDummy020 A B))).fv ∪ ((Class.cv (alphaDummy021 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0019 (x : Var) (y : Var) :
    (alphaDummy023 x y) ∈
      (((Class.cv (alphaDummy023 x y))).fv ∪ ((Class.cv (alphaDummy024 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0020 (A : Class) (B : Class) :
    (alphaDummy021 A B) ∈
      (((synCnin (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B)))).fv ∪
        ((synCnin (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0021 (x : Var) (y : Var) :
    (alphaDummy024 x y) ∈
      (((synCnin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))).fv ∪
        ((synCnin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0022 (A : Class) (B : Class) :
    (alphaDummy021 A B) ∈
      (((Class.cv (alphaDummy020 A B))).fv ∪ ((Class.cv (alphaDummy021 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0023 (x : Var) (y : Var) :
    (alphaDummy024 x y) ∈
      (((Class.cv (alphaDummy023 x y))).fv ∪ ((Class.cv (alphaDummy024 x y))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0024 (A : Class) (B : Class) :
    (alphaDummy020 A B) ∈
      (((synCcompl (Class.cv (alphaDummy020 A B)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy021 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0025 (x : Var) (y : Var) :
    (alphaDummy023 x y) ∈
      (((synCcompl (Class.cv (alphaDummy023 x y)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy024 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0026 (A : Class) (B : Class) :
    (alphaDummy020 A B) ∈
      (((Class.cv (alphaDummy020 A B))).fv ∪ ((Class.cv (alphaDummy020 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0027 (x : Var) (y : Var) :
    (alphaDummy023 x y) ∈
      (((Class.cv (alphaDummy023 x y))).fv ∪ ((Class.cv (alphaDummy023 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0028 (A : Class) (B : Class) :
    (alphaDummy021 A B) ∈
      (((synCcompl (Class.cv (alphaDummy020 A B)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy021 A B)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0029 (x : Var) (y : Var) :
    (alphaDummy024 x y) ∈
      (((synCcompl (Class.cv (alphaDummy023 x y)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy024 x y)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0030 (A : Class) (B : Class) :
    (alphaDummy021 A B) ∈
      (((Class.cv (alphaDummy021 A B))).fv ∪ ((Class.cv (alphaDummy021 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0031 (x : Var) (y : Var) :
    (alphaDummy024 x y) ∈
      (((Class.cv (alphaDummy024 x y))).fv ∪ ((Class.cv (alphaDummy024 x y))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0032 (A : Class) (B : Class) :
    (alphaDummy001 A B) ∈
      (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0033 (A : Class) (B : Class) :
    (alphaDummy001 A B) ∈
      (((synCcompl (Class.cab (alphaDummy005 A B)
              (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy000 A B))
                (Wff.classEq (Class.cv (alphaDummy005 A B))
                  (synCphi (Class.cv (alphaDummy006 A B)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy005 A B)
              (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy001 A B))
                (Wff.classEq (Class.cv (alphaDummy005 A B))
                  (synCun (synCphi (Class.cv (alphaDummy006 A B)))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy007 x y)
              (synWrex (alphaDummy008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (alphaDummy007 x y))
                  (synCphi (Class.cv (alphaDummy008 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (alphaDummy007 x y))
                  (synCun (synCphi (Class.cv (alphaDummy008 x y)))
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

theorem support_mem_0036 (A : Class) (B : Class) :
    (alphaDummy001 A B) ∈
      (((Class.cab (alphaDummy005 A B)
            (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy001 A B))
              (Wff.classEq (Class.cv (alphaDummy005 A B))
                (synCun (synCphi (Class.cv (alphaDummy006 A B)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy005 A B)
            (synWrex (alphaDummy006 A B) (Class.cv (alphaDummy001 A B))
              (Wff.classEq (Class.cv (alphaDummy005 A B))
                (synCun (synCphi (Class.cv (alphaDummy006 A B)))
                  (synCsn (synC0c))))))).fv) :=
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
      (((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy007 x y))
                (synCun (synCphi (Class.cv (alphaDummy008 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy007 x y)
            (synWrex (alphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy007 x y))
                (synCun (synCphi (Class.cv (alphaDummy008 x y)))
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

theorem support_mem_0038 (A : Class) (B : Class) :
    (alphaDummy006 A B) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy006 A B))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0039 (x : Var) (y : Var) :
    (alphaDummy008 x y) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy008 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0040 (A : Class) (B : Class) :
    (alphaDummy006 A B) ∈
      (((synCphi (Class.cv (alphaDummy006 A B)))).fv ∪
        ((synCphi (Class.cv (alphaDummy006 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0041 (x : Var) (y : Var) :
    (alphaDummy008 x y) ∈
      (((synCphi (Class.cv (alphaDummy008 x y)))).fv ∪
        ((synCphi (Class.cv (alphaDummy008 x y)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0042 (A : Class) (B : Class) :
    (alphaDummy000 A B) ∈
      (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy002 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0043 (A : Class) (B : Class) :
    (alphaDummy000 A B) ∈
      (((synCcompl (Class.cab (alphaDummy041 A B)
              (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy000 A B))
                (Wff.classEq (Class.cv (alphaDummy041 A B))
                  (synCphi (Class.cv (alphaDummy042 A B)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy041 A B)
              (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy002 A B))
                (Wff.classEq (Class.cv (alphaDummy041 A B))
                  (synCun (synCphi (Class.cv (alphaDummy042 A B)))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy043 x z)
              (synWrex (alphaDummy044 x z) (Class.cv x)
                (Wff.classEq (Class.cv (alphaDummy043 x z))
                  (synCphi (Class.cv (alphaDummy044 x z)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy043 x z))
                  (synCun (synCphi (Class.cv (alphaDummy044 x z)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (alphaDummy000 A B) ∈
      (((Class.cab (alphaDummy041 A B)
            (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy000 A B))
              (Wff.classEq (Class.cv (alphaDummy041 A B))
                (synCphi (Class.cv (alphaDummy042 A B))))))).fv ∪
        ((Class.cab (alphaDummy041 A B)
            (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy000 A B))
              (Wff.classEq (Class.cv (alphaDummy041 A B))
                (synCphi (Class.cv (alphaDummy042 A B))))))).fv) :=
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
      (((Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy043 x z))
                (synCphi (Class.cv (alphaDummy044 x z))))))).fv ∪
        ((Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv x)
              (Wff.classEq (Class.cv (alphaDummy043 x z))
                (synCphi (Class.cv (alphaDummy044 x z))))))).fv) :=
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
    (alphaDummy042 A B) ∈ (((Class.cv (alphaDummy042 A B))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0049 (x : Var) (z : Var) :
    (alphaDummy044 x z) ∈ (((Class.cv (alphaDummy044 x z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0050 (A : Class) (B : Class) :
    (alphaDummy049 A B) ∈
      (((Wff.classMem (Class.cv (alphaDummy049 A B)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy049 A B)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy049 A B))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0051 (x : Var) (z : Var) :
    (alphaDummy051 x z) ∈
      (((Wff.classMem (Class.cv (alphaDummy051 x z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy051 x z)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy051 x z))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0052 (A : Class) (B : Class) :
    (alphaDummy049 A B) ∈ (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0053 (x : Var) (z : Var) :
    (alphaDummy051 x z) ∈ (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0054 (A : Class) (B : Class) :
    (alphaDummy056 A B) ∈
      (((synCnin (Class.cv (alphaDummy056 A B)) (Class.cv (alphaDummy057 A B)))).fv ∪
        ((synCnin (Class.cv (alphaDummy056 A B)) (Class.cv (alphaDummy057 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0055 (x : Var) (z : Var) :
    (alphaDummy059 x z) ∈
      (((synCnin (Class.cv (alphaDummy059 x z)) (Class.cv (alphaDummy060 x z)))).fv ∪
        ((synCnin (Class.cv (alphaDummy059 x z)) (Class.cv (alphaDummy060 x z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0056 (A : Class) (B : Class) :
    (alphaDummy056 A B) ∈
      (((Class.cv (alphaDummy056 A B))).fv ∪ ((Class.cv (alphaDummy057 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0057 (x : Var) (z : Var) :
    (alphaDummy059 x z) ∈
      (((Class.cv (alphaDummy059 x z))).fv ∪ ((Class.cv (alphaDummy060 x z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0058 (A : Class) (B : Class) :
    (alphaDummy057 A B) ∈
      (((synCnin (Class.cv (alphaDummy056 A B)) (Class.cv (alphaDummy057 A B)))).fv ∪
        ((synCnin (Class.cv (alphaDummy056 A B)) (Class.cv (alphaDummy057 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0059 (x : Var) (z : Var) :
    (alphaDummy060 x z) ∈
      (((synCnin (Class.cv (alphaDummy059 x z)) (Class.cv (alphaDummy060 x z)))).fv ∪
        ((synCnin (Class.cv (alphaDummy059 x z)) (Class.cv (alphaDummy060 x z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0060 (A : Class) (B : Class) :
    (alphaDummy057 A B) ∈
      (((Class.cv (alphaDummy056 A B))).fv ∪ ((Class.cv (alphaDummy057 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0061 (x : Var) (z : Var) :
    (alphaDummy060 x z) ∈
      (((Class.cv (alphaDummy059 x z))).fv ∪ ((Class.cv (alphaDummy060 x z))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0062 (A : Class) (B : Class) :
    (alphaDummy056 A B) ∈
      (((synCcompl (Class.cv (alphaDummy056 A B)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy057 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0063 (x : Var) (z : Var) :
    (alphaDummy059 x z) ∈
      (((synCcompl (Class.cv (alphaDummy059 x z)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy060 x z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0064 (A : Class) (B : Class) :
    (alphaDummy056 A B) ∈
      (((Class.cv (alphaDummy056 A B))).fv ∪ ((Class.cv (alphaDummy056 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0065 (x : Var) (z : Var) :
    (alphaDummy059 x z) ∈
      (((Class.cv (alphaDummy059 x z))).fv ∪ ((Class.cv (alphaDummy059 x z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0066 (A : Class) (B : Class) :
    (alphaDummy057 A B) ∈
      (((synCcompl (Class.cv (alphaDummy056 A B)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy057 A B)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0067 (x : Var) (z : Var) :
    (alphaDummy060 x z) ∈
      (((synCcompl (Class.cv (alphaDummy059 x z)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy060 x z)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0068 (A : Class) (B : Class) :
    (alphaDummy057 A B) ∈
      (((Class.cv (alphaDummy057 A B))).fv ∪ ((Class.cv (alphaDummy057 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0069 (x : Var) (z : Var) :
    (alphaDummy060 x z) ∈
      (((Class.cv (alphaDummy060 x z))).fv ∪ ((Class.cv (alphaDummy060 x z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0070 (A : Class) (B : Class) :
    (alphaDummy002 A B) ∈
      (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy002 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0071 (A : Class) (B : Class) :
    (alphaDummy002 A B) ∈
      (((synCcompl (Class.cab (alphaDummy041 A B)
              (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy000 A B))
                (Wff.classEq (Class.cv (alphaDummy041 A B))
                  (synCphi (Class.cv (alphaDummy042 A B)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy041 A B)
              (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy002 A B))
                (Wff.classEq (Class.cv (alphaDummy041 A B))
                  (synCun (synCphi (Class.cv (alphaDummy042 A B)))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy043 x z)
              (synWrex (alphaDummy044 x z) (Class.cv x)
                (Wff.classEq (Class.cv (alphaDummy043 x z))
                  (synCphi (Class.cv (alphaDummy044 x z)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy043 x z))
                  (synCun (synCphi (Class.cv (alphaDummy044 x z)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (alphaDummy002 A B) ∈
      (((Class.cab (alphaDummy041 A B)
            (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy002 A B))
              (Wff.classEq (Class.cv (alphaDummy041 A B))
                (synCun (synCphi (Class.cv (alphaDummy042 A B)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy041 A B)
            (synWrex (alphaDummy042 A B) (Class.cv (alphaDummy002 A B))
              (Wff.classEq (Class.cv (alphaDummy041 A B))
                (synCun (synCphi (Class.cv (alphaDummy042 A B)))
                  (synCsn (synC0c))))))).fv) :=
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
      (((Class.cab (alphaDummy043 x z) (synWrex (alphaDummy044 x z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy043 x z))
                (synCun (synCphi (Class.cv (alphaDummy044 x z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy043 x z)
            (synWrex (alphaDummy044 x z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy043 x z))
                (synCun (synCphi (Class.cv (alphaDummy044 x z)))
                  (synCsn (synC0c))))))).fv) :=
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
    (alphaDummy042 A B) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy042 A B))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0077 (x : Var) (z : Var) :
    (alphaDummy044 x z) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy044 x z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0078 (A : Class) (B : Class) :
    (alphaDummy042 A B) ∈
      (((synCphi (Class.cv (alphaDummy042 A B)))).fv ∪
        ((synCphi (Class.cv (alphaDummy042 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0079 (x : Var) (z : Var) :
    (alphaDummy044 x z) ∈
      (((synCphi (Class.cv (alphaDummy044 x z)))).fv ∪
        ((synCphi (Class.cv (alphaDummy044 x z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0080 (A : Class) (B : Class) :
    (alphaDummy002 A B) ∈
      (((Class.cv (alphaDummy002 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0081 (A : Class) (B : Class) :
    (alphaDummy002 A B) ∈
      (((synCcompl (Class.cab (alphaDummy077 A B)
              (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy002 A B))
                (Wff.classEq (Class.cv (alphaDummy077 A B))
                  (synCphi (Class.cv (alphaDummy078 A B)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy077 A B)
              (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy001 A B))
                (Wff.classEq (Class.cv (alphaDummy077 A B))
                  (synCun (synCphi (Class.cv (alphaDummy078 A B)))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy079 y z)
              (synWrex (alphaDummy080 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy079 y z))
                  (synCphi (Class.cv (alphaDummy080 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv y)
                (Wff.classEq (Class.cv (alphaDummy079 y z))
                  (synCun (synCphi (Class.cv (alphaDummy080 y z)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (alphaDummy002 A B) ∈
      (((Class.cab (alphaDummy077 A B)
            (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy002 A B))
              (Wff.classEq (Class.cv (alphaDummy077 A B))
                (synCphi (Class.cv (alphaDummy078 A B))))))).fv ∪
        ((Class.cab (alphaDummy077 A B)
            (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy002 A B))
              (Wff.classEq (Class.cv (alphaDummy077 A B))
                (synCphi (Class.cv (alphaDummy078 A B))))))).fv) :=
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
      (((Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy079 y z))
                (synCphi (Class.cv (alphaDummy080 y z))))))).fv ∪
        ((Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy079 y z))
                (synCphi (Class.cv (alphaDummy080 y z))))))).fv) :=
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
    (alphaDummy078 A B) ∈ (((Class.cv (alphaDummy078 A B))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0087 (y : Var) (z : Var) :
    (alphaDummy080 y z) ∈ (((Class.cv (alphaDummy080 y z))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0088 (A : Class) (B : Class) :
    (alphaDummy085 A B) ∈
      (((Wff.classMem (Class.cv (alphaDummy085 A B)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy085 A B)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy085 A B))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0089 (y : Var) (z : Var) :
    (alphaDummy087 y z) ∈
      (((Wff.classMem (Class.cv (alphaDummy087 y z)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy087 y z)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy087 y z))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0090 (A : Class) (B : Class) :
    (alphaDummy085 A B) ∈ (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0091 (y : Var) (z : Var) :
    (alphaDummy087 y z) ∈ (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0092 (A : Class) (B : Class) :
    (alphaDummy092 A B) ∈
      (((synCnin (Class.cv (alphaDummy092 A B)) (Class.cv (alphaDummy093 A B)))).fv ∪
        ((synCnin (Class.cv (alphaDummy092 A B)) (Class.cv (alphaDummy093 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0093 (y : Var) (z : Var) :
    (alphaDummy095 y z) ∈
      (((synCnin (Class.cv (alphaDummy095 y z)) (Class.cv (alphaDummy096 y z)))).fv ∪
        ((synCnin (Class.cv (alphaDummy095 y z)) (Class.cv (alphaDummy096 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0094 (A : Class) (B : Class) :
    (alphaDummy092 A B) ∈
      (((Class.cv (alphaDummy092 A B))).fv ∪ ((Class.cv (alphaDummy093 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0095 (y : Var) (z : Var) :
    (alphaDummy095 y z) ∈
      (((Class.cv (alphaDummy095 y z))).fv ∪ ((Class.cv (alphaDummy096 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0096 (A : Class) (B : Class) :
    (alphaDummy093 A B) ∈
      (((synCnin (Class.cv (alphaDummy092 A B)) (Class.cv (alphaDummy093 A B)))).fv ∪
        ((synCnin (Class.cv (alphaDummy092 A B)) (Class.cv (alphaDummy093 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0097 (y : Var) (z : Var) :
    (alphaDummy096 y z) ∈
      (((synCnin (Class.cv (alphaDummy095 y z)) (Class.cv (alphaDummy096 y z)))).fv ∪
        ((synCnin (Class.cv (alphaDummy095 y z)) (Class.cv (alphaDummy096 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0098 (A : Class) (B : Class) :
    (alphaDummy093 A B) ∈
      (((Class.cv (alphaDummy092 A B))).fv ∪ ((Class.cv (alphaDummy093 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0099 (y : Var) (z : Var) :
    (alphaDummy096 y z) ∈
      (((Class.cv (alphaDummy095 y z))).fv ∪ ((Class.cv (alphaDummy096 y z))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0100 (A : Class) (B : Class) :
    (alphaDummy092 A B) ∈
      (((synCcompl (Class.cv (alphaDummy092 A B)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy093 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0101 (y : Var) (z : Var) :
    (alphaDummy095 y z) ∈
      (((synCcompl (Class.cv (alphaDummy095 y z)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy096 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0102 (A : Class) (B : Class) :
    (alphaDummy092 A B) ∈
      (((Class.cv (alphaDummy092 A B))).fv ∪ ((Class.cv (alphaDummy092 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0103 (y : Var) (z : Var) :
    (alphaDummy095 y z) ∈
      (((Class.cv (alphaDummy095 y z))).fv ∪ ((Class.cv (alphaDummy095 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0104 (A : Class) (B : Class) :
    (alphaDummy093 A B) ∈
      (((synCcompl (Class.cv (alphaDummy092 A B)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy093 A B)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0105 (y : Var) (z : Var) :
    (alphaDummy096 y z) ∈
      (((synCcompl (Class.cv (alphaDummy095 y z)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy096 y z)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0106 (A : Class) (B : Class) :
    (alphaDummy093 A B) ∈
      (((Class.cv (alphaDummy093 A B))).fv ∪ ((Class.cv (alphaDummy093 A B))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0107 (y : Var) (z : Var) :
    (alphaDummy096 y z) ∈
      (((Class.cv (alphaDummy096 y z))).fv ∪ ((Class.cv (alphaDummy096 y z))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0108 (A : Class) (B : Class) :
    (alphaDummy001 A B) ∈
      (((Class.cv (alphaDummy002 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0109 (A : Class) (B : Class) :
    (alphaDummy001 A B) ∈
      (((synCcompl (Class.cab (alphaDummy077 A B)
              (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy002 A B))
                (Wff.classEq (Class.cv (alphaDummy077 A B))
                  (synCphi (Class.cv (alphaDummy078 A B)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy077 A B)
              (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy001 A B))
                (Wff.classEq (Class.cv (alphaDummy077 A B))
                  (synCun (synCphi (Class.cv (alphaDummy078 A B)))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy079 y z)
              (synWrex (alphaDummy080 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy079 y z))
                  (synCphi (Class.cv (alphaDummy080 y z)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv y)
                (Wff.classEq (Class.cv (alphaDummy079 y z))
                  (synCun (synCphi (Class.cv (alphaDummy080 y z)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (alphaDummy001 A B) ∈
      (((Class.cab (alphaDummy077 A B)
            (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy001 A B))
              (Wff.classEq (Class.cv (alphaDummy077 A B))
                (synCun (synCphi (Class.cv (alphaDummy078 A B)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy077 A B)
            (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy001 A B))
              (Wff.classEq (Class.cv (alphaDummy077 A B))
                (synCun (synCphi (Class.cv (alphaDummy078 A B)))
                  (synCsn (synC0c))))))).fv) :=
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
      (((Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy079 y z))
                (synCun (synCphi (Class.cv (alphaDummy080 y z)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy079 y z)
            (synWrex (alphaDummy080 y z) (Class.cv y)
              (Wff.classEq (Class.cv (alphaDummy079 y z))
                (synCun (synCphi (Class.cv (alphaDummy080 y z)))
                  (synCsn (synC0c))))))).fv) :=
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
    (alphaDummy078 A B) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy078 A B))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0115 (y : Var) (z : Var) :
    (alphaDummy080 y z) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy080 y z))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0116 (A : Class) (B : Class) :
    (alphaDummy078 A B) ∈
      (((synCphi (Class.cv (alphaDummy078 A B)))).fv ∪
        ((synCphi (Class.cv (alphaDummy078 A B)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0117 (y : Var) (z : Var) :
    (alphaDummy080 y z) ∈
      (((synCphi (Class.cv (alphaDummy080 y z)))).fv ∪
        ((synCphi (Class.cv (alphaDummy080 y z)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem focused_notmem_0000 (A : Class) (B : Class) : (alphaDummy002 A B) ∉ B.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 2 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_right _ (hu))

theorem focused_notmem_0001 (A : Class) (B : Class) : (alphaDummy003 A B) ∉ B.fv :=
  by
  change
    freshVar
        (({(alphaDummy000 A B)} : Finset Var) ∪ ({(alphaDummy001 A B)} : Finset Var) ∪
          ((synWex (alphaDummy002 A B) (synWa (synWbr (Class.cv (alphaDummy000 A B)) B
                  (Class.cv (alphaDummy002 A B))) (synWbr (Class.cv (alphaDummy002 A B)) A
                  (Class.cv (alphaDummy001 A B)))))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wex (alphaDummy002 A B) (synWa
                  (synWbr (Class.cv (alphaDummy000 A B)) B (Class.cv (alphaDummy002 A B)))
                  (synWbr (Class.cv (alphaDummy002 A B)) A
                    (Class.cv (alphaDummy001 A B))))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => ((focused_notmem_0000 A B)) (h_eq ▸ hu)), (((fv_syn_wa
                      (synWbr (Class.cv (alphaDummy000 A B)) B
                        (Class.cv (alphaDummy002 A B)))
                      (synWbr (Class.cv (alphaDummy002 A B)) A
                        (Class.cv (alphaDummy001 A B)))).symm ▸ (Finset.mem_union_left _
                    (((fv_syn_wbr (Class.cv (alphaDummy000 A B)) B
                          (Class.cv (alphaDummy002 A B))).symm ▸
                      (Finset.mem_union_right _ (hu)))))))⟩))))

theorem wpp_notmem_0196 (A : Class) (B : Class) : (alphaDummy003 A B) ∉ (B).fv := by
  exact (focused_notmem_0001 A B)

theorem focused_notmem_0002 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_B_z : z ∉ B.fv) : (alphaDummy004 x y z A B) ∉ B.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z
              (synWa (synWbr (Class.cv x) B (Class.cv z))
                (synWbr (Class.cv z) A (Class.cv y))))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wex z
                (synWa (synWbr (Class.cv x) B (Class.cv z))
                  (synWbr (Class.cv z) A (Class.cv y)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (dv_B_z) (h_eq ▸ hu)),
                (((fv_syn_wa (synWbr (Class.cv x) B (Class.cv z))
                      (synWbr (Class.cv z) A (Class.cv y))).symm ▸ (Finset.mem_union_left _
                    (((fv_syn_wbr (Class.cv x) B (Class.cv z)).symm ▸
                      (Finset.mem_union_right _ (hu)))))))⟩))))

theorem wpp_notmem_0197 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_B_z : z ∉ B.fv) : (alphaDummy004 x y z A B) ∉ (B).fv := by
  exact (focused_notmem_0002 x y z A B dv_B_z)

theorem focused_notmem_0003 (A : Class) (B : Class) : (alphaDummy000 A B) ∉ B.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem wpp_notmem_0198 (A : Class) (B : Class) : (alphaDummy000 A B) ∉ (B).fv := by
  exact (focused_notmem_0003 A B)

theorem wpp_notmem_0199 (x : Var) (B : Class) (dv_B_x : x ∉ B.fv) : x ∉ (B).fv := by
  exact dv_B_x

theorem focused_notmem_0004 (A : Class) (B : Class) : (alphaDummy001 A B) ∉ B.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 1 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem wpp_notmem_0200 (A : Class) (B : Class) : (alphaDummy001 A B) ∉ (B).fv := by
  exact (focused_notmem_0004 A B)

theorem wpp_notmem_0201 (y : Var) (B : Class) (dv_B_y : y ∉ B.fv) : y ∉ (B).fv := by
  exact dv_B_y

theorem wpp_notmem_0202 (A : Class) (B : Class) : (alphaDummy002 A B) ∉ (B).fv := by
  exact (focused_notmem_0000 A B)

theorem wpp_notmem_0203 (z : Var) (B : Class) (dv_B_z : z ∉ B.fv) : z ∉ (B).fv := by
  exact dv_B_z

theorem focused_notmem_0005 (A : Class) (B : Class) : (alphaDummy002 A B) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_left _ (hu))

theorem focused_notmem_0006 (A : Class) (B : Class) : (alphaDummy003 A B) ∉ A.fv :=
  by
  change
    freshVar
        (({(alphaDummy000 A B)} : Finset Var) ∪ ({(alphaDummy001 A B)} : Finset Var) ∪
          ((synWex (alphaDummy002 A B) (synWa (synWbr (Class.cv (alphaDummy000 A B)) B
                  (Class.cv (alphaDummy002 A B))) (synWbr (Class.cv (alphaDummy002 A B)) A
                  (Class.cv (alphaDummy001 A B)))))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wex (alphaDummy002 A B) (synWa
                  (synWbr (Class.cv (alphaDummy000 A B)) B (Class.cv (alphaDummy002 A B)))
                  (synWbr (Class.cv (alphaDummy002 A B)) A
                    (Class.cv (alphaDummy001 A B))))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => ((focused_notmem_0005 A B)) (h_eq ▸ hu)), (((fv_syn_wa
                      (synWbr (Class.cv (alphaDummy000 A B)) B
                        (Class.cv (alphaDummy002 A B)))
                      (synWbr (Class.cv (alphaDummy002 A B)) A
                        (Class.cv (alphaDummy001 A B)))).symm ▸ (Finset.mem_union_right _
                    (((fv_syn_wbr (Class.cv (alphaDummy002 A B)) A
                          (Class.cv (alphaDummy001 A B))).symm ▸
                      (Finset.mem_union_right _ (hu)))))))⟩))))

theorem wpp_notmem_0286 (A : Class) (B : Class) : (alphaDummy003 A B) ∉ (A).fv := by
  exact (focused_notmem_0006 A B)

theorem focused_notmem_0007 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) : (alphaDummy004 x y z A B) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z
              (synWa (synWbr (Class.cv x) B (Class.cv z))
                (synWbr (Class.cv z) A (Class.cv y))))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wex z
                (synWa (synWbr (Class.cv x) B (Class.cv z))
                  (synWbr (Class.cv z) A (Class.cv y)))).symm ▸ (Finset.mem_erase.mpr
              ⟨(fun h_eq => (dv_A_z) (h_eq ▸ hu)),
                (((fv_syn_wa (synWbr (Class.cv x) B (Class.cv z))
                      (synWbr (Class.cv z) A (Class.cv y))).symm ▸ (Finset.mem_union_right _
                    (((fv_syn_wbr (Class.cv z) A (Class.cv y)).symm ▸
                      (Finset.mem_union_right _ (hu)))))))⟩))))

theorem wpp_notmem_0287 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) : (alphaDummy004 x y z A B) ∉ (A).fv := by
  exact (focused_notmem_0007 x y z A B dv_A_z)

theorem focused_notmem_0008 (A : Class) (B : Class) : (alphaDummy000 A B) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem wpp_notmem_0288 (A : Class) (B : Class) : (alphaDummy000 A B) ∉ (A).fv := by
  exact (focused_notmem_0008 A B)

theorem wpp_notmem_0289 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem focused_notmem_0009 (A : Class) (B : Class) : (alphaDummy001 A B) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (hu))

theorem wpp_notmem_0290 (A : Class) (B : Class) : (alphaDummy001 A B) ∉ (A).fv := by
  exact (focused_notmem_0009 A B)

theorem wpp_notmem_0291 (y : Var) (A : Class) (dv_A_y : y ∉ A.fv) : y ∉ (A).fv := by
  exact dv_A_y

theorem wpp_notmem_0292 (A : Class) (B : Class) : (alphaDummy002 A B) ∉ (A).fv := by
  exact (focused_notmem_0005 A B)

theorem wpp_notmem_0293 (z : Var) (A : Class) (dv_A_z : z ∉ A.fv) : z ∉ (A).fv := by
  exact dv_A_z

end CompositionAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
