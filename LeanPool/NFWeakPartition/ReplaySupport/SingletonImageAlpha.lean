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

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_000`. -/
@[expose]
def alphaDummy000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_001`. -/
@[expose]
def alphaDummy001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_002`. -/
@[expose]
def alphaDummy002 (A : Class) : Var :=
  (freshVar ((A).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_003`. -/
@[expose]
def alphaDummy003 (A : Class) : Var :=
  (freshVar ((A).fv) 3)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_004`. -/
@[expose]
def alphaDummy004 (A : Class) : Var :=
  (freshVar (({(alphaDummy001 A)} : Finset Var) ∪ ({(alphaDummy002 A)} : Finset Var) ∪
      ((synWex (alphaDummy003 A) (synWex (alphaDummy000 A) (synW3a
              (Wff.classEq (Class.cv (alphaDummy001 A))
                (synCsn (Class.cv (alphaDummy003 A))))
              (Wff.classEq (Class.cv (alphaDummy002 A))
                (synCsn (Class.cv (alphaDummy000 A))))
              (synWbr (Class.cv (alphaDummy003 A)) A (Class.cv (alphaDummy000 A))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_005`. -/
@[expose]
def alphaDummy005 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z (synWex w
            (synW3a (Wff.classEq (Class.cv x) (synCsn (Class.cv z)))
              (Wff.classEq (Class.cv y) (synCsn (Class.cv w)))
              (synWbr (Class.cv z) A (Class.cv w)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_006`. -/
@[expose]
def alphaDummy006 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy001 A))).fv ∪ ((Class.cv (alphaDummy002 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_007`. -/
@[expose]
def alphaDummy007 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy001 A))).fv ∪ ((Class.cv (alphaDummy002 A))).fv) 1)

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
def alphaDummy010 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy006 A)
            (synWrex (alphaDummy007 A) (Class.cv (alphaDummy001 A))
              (Wff.classEq (Class.cv (alphaDummy006 A))
                (synCphi (Class.cv (alphaDummy007 A)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy006 A)
            (synWrex (alphaDummy007 A) (Class.cv (alphaDummy002 A))
              (Wff.classEq (Class.cv (alphaDummy006 A))
                (synCun (synCphi (Class.cv (alphaDummy007 A))) (synCsn (synC0c)))))))).fv)
    0)

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
def alphaDummy012 (A : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy006 A)
          (synWrex (alphaDummy007 A) (Class.cv (alphaDummy001 A))
            (Wff.classEq (Class.cv (alphaDummy006 A))
              (synCphi (Class.cv (alphaDummy007 A))))))).fv ∪ ((Class.cab (alphaDummy006 A)
          (synWrex (alphaDummy007 A) (Class.cv (alphaDummy001 A))
            (Wff.classEq (Class.cv (alphaDummy006 A))
              (synCphi (Class.cv (alphaDummy007 A))))))).fv) 0)

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
def alphaDummy014 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy007 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_015`. -/
@[expose]
def alphaDummy015 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy007 A))).fv) 1)

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
def alphaDummy018 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy014 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy014 A)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy014 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_019`. -/
@[expose]
def alphaDummy019 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy016 x y)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy016 x y)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy016 x y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_020`. -/
@[expose]
def alphaDummy020 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_021`. -/
@[expose]
def alphaDummy021 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_022`. -/
@[expose]
def alphaDummy022 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv) 2)

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
def alphaDummy036 (A : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy006 A)
          (synWrex (alphaDummy007 A) (Class.cv (alphaDummy002 A))
            (Wff.classEq (Class.cv (alphaDummy006 A))
              (synCun (synCphi (Class.cv (alphaDummy007 A))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy006 A)
          (synWrex (alphaDummy007 A) (Class.cv (alphaDummy002 A))
            (Wff.classEq (Class.cv (alphaDummy006 A))
              (synCun (synCphi (Class.cv (alphaDummy007 A))) (synCsn (synC0c))))))).fv) 0)

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
def alphaDummy038 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy007 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_039`. -/
@[expose]
def alphaDummy039 (x : Var) (y : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy009 x y))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_040`. -/
@[expose]
def alphaDummy040 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy007 A)))).fv ∪
      ((synCphi (Class.cv (alphaDummy007 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_041`. -/
@[expose]
def alphaDummy041 (x : Var) (y : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy009 x y)))).fv ∪
      ((synCphi (Class.cv (alphaDummy009 x y)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_046`. -/
@[expose]
def alphaDummy046 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy003 A))).fv ∪ ((Class.cv (alphaDummy000 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_047`. -/
@[expose]
def alphaDummy047 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy003 A))).fv ∪ ((Class.cv (alphaDummy000 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_048`. -/
@[expose]
def alphaDummy048 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_049`. -/
@[expose]
def alphaDummy049 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv z)).fv ∪ ((Class.cv w)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_050`. -/
@[expose]
def alphaDummy050 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy046 A)
            (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
              (Wff.classEq (Class.cv (alphaDummy046 A))
                (synCphi (Class.cv (alphaDummy047 A)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy046 A)
            (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
              (Wff.classEq (Class.cv (alphaDummy046 A))
                (synCun (synCphi (Class.cv (alphaDummy047 A))) (synCsn (synC0c)))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_051`. -/
@[expose]
def alphaDummy051 (z : Var) (w : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (alphaDummy048 z w)
            (synWrex (alphaDummy049 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy048 z w))
                (synCphi (Class.cv (alphaDummy049 z w)))))))).fv ∪ ((synCcompl
          (Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy048 z w))
                (synCun (synCphi (Class.cv (alphaDummy049 z w)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_052`. -/
@[expose]
def alphaDummy052 (A : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy046 A)
          (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
            (Wff.classEq (Class.cv (alphaDummy046 A))
              (synCphi (Class.cv (alphaDummy047 A))))))).fv ∪ ((Class.cab (alphaDummy046 A)
          (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
            (Wff.classEq (Class.cv (alphaDummy046 A))
              (synCphi (Class.cv (alphaDummy047 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_053`. -/
@[expose]
def alphaDummy053 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy048 z w))
              (synCphi (Class.cv (alphaDummy049 z w))))))).fv ∪
      ((Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv z)
            (Wff.classEq (Class.cv (alphaDummy048 z w))
              (synCphi (Class.cv (alphaDummy049 z w))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_054`. -/
@[expose]
def alphaDummy054 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy047 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_055`. -/
@[expose]
def alphaDummy055 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy047 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_056`. -/
@[expose]
def alphaDummy056 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy049 z w))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_057`. -/
@[expose]
def alphaDummy057 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy049 z w))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_058`. -/
@[expose]
def alphaDummy058 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy054 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy054 A)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy054 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_059`. -/
@[expose]
def alphaDummy059 (z : Var) (w : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (alphaDummy056 z w)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (alphaDummy056 z w)) (synC1c))).fv ∪
      ((Class.cv (alphaDummy056 z w))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_060`. -/
@[expose]
def alphaDummy060 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_061`. -/
@[expose]
def alphaDummy061 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_062`. -/
@[expose]
def alphaDummy062 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_063`. -/
@[expose]
def alphaDummy063 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_064`. -/
@[expose]
def alphaDummy064 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_065`. -/
@[expose]
def alphaDummy065 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_076`. -/
@[expose]
def alphaDummy076 (A : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy046 A)
          (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
            (Wff.classEq (Class.cv (alphaDummy046 A))
              (synCun (synCphi (Class.cv (alphaDummy047 A))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy046 A)
          (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
            (Wff.classEq (Class.cv (alphaDummy046 A))
              (synCun (synCphi (Class.cv (alphaDummy047 A))) (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_077`. -/
@[expose]
def alphaDummy077 (z : Var) (w : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alphaDummy048 z w))
              (synCun (synCphi (Class.cv (alphaDummy049 z w))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv w)
            (Wff.classEq (Class.cv (alphaDummy048 z w))
              (synCun (synCphi (Class.cv (alphaDummy049 z w))) (synCsn (synC0c))))))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_078`. -/
@[expose]
def alphaDummy078 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy047 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_079`. -/
@[expose]
def alphaDummy079 (z : Var) (w : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy049 z w))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_080`. -/
@[expose]
def alphaDummy080 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy047 A)))).fv ∪
      ((synCphi (Class.cv (alphaDummy047 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_081`. -/
@[expose]
def alphaDummy081 (z : Var) (w : Var) : Var :=
  (freshVar (((synCphi (Class.cv (alphaDummy049 z w)))).fv ∪
      ((synCphi (Class.cv (alphaDummy049 z w)))).fv) 0)

theorem mem_pair_support_left (u v : Var) (support : Finset Var) :
    u ∈ ({ u } ∪ { v } ∪ support) :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))

theorem mem_pair_support_right (u v : Var) (support : Finset Var) :
    v ∈ ({ u } ∪ { v } ∪ support) :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem support_mem_0000 (A : Class) :
    (alphaDummy001 A) ∈
      (({(alphaDummy001 A)} : Finset Var) ∪ ({(alphaDummy002 A)} : Finset Var) ∪
        ((synWex (alphaDummy003 A) (synWex (alphaDummy000 A) (synW3a
                (Wff.classEq (Class.cv (alphaDummy001 A))
                  (synCsn (Class.cv (alphaDummy003 A))))
                (Wff.classEq (Class.cv (alphaDummy002 A))
                  (synCsn (Class.cv (alphaDummy000 A))))
                (synWbr (Class.cv (alphaDummy003 A)) A
                  (Class.cv (alphaDummy000 A))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_left (alphaDummy001 A) (alphaDummy002 A)
        ((synWex (alphaDummy003 A) (synWex (alphaDummy000 A) (synW3a
                (Wff.classEq (Class.cv (alphaDummy001 A))
                  (synCsn (Class.cv (alphaDummy003 A))))
                (Wff.classEq (Class.cv (alphaDummy002 A))
                  (synCsn (Class.cv (alphaDummy000 A))))
                (synWbr (Class.cv (alphaDummy003 A)) A (Class.cv (alphaDummy000 A))))))).fv

theorem support_mem_0001 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z (synWex w
              (synW3a (Wff.classEq (Class.cv x) (synCsn (Class.cv z)))
                (Wff.classEq (Class.cv y) (synCsn (Class.cv w)))
                (synWbr (Class.cv z) A (Class.cv w)))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_left x y
        ((synWex z (synWex w (synW3a (Wff.classEq (Class.cv x) (synCsn (Class.cv z)))
                (Wff.classEq (Class.cv y) (synCsn (Class.cv w)))
                (synWbr (Class.cv z) A (Class.cv w)))))).fv

theorem support_mem_0002 (A : Class) :
    (alphaDummy002 A) ∈
      (({(alphaDummy001 A)} : Finset Var) ∪ ({(alphaDummy002 A)} : Finset Var) ∪
        ((synWex (alphaDummy003 A) (synWex (alphaDummy000 A) (synW3a
                (Wff.classEq (Class.cv (alphaDummy001 A))
                  (synCsn (Class.cv (alphaDummy003 A))))
                (Wff.classEq (Class.cv (alphaDummy002 A))
                  (synCsn (Class.cv (alphaDummy000 A))))
                (synWbr (Class.cv (alphaDummy003 A)) A
                  (Class.cv (alphaDummy000 A))))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_right (alphaDummy001 A) (alphaDummy002 A)
        ((synWex (alphaDummy003 A) (synWex (alphaDummy000 A) (synW3a
                (Wff.classEq (Class.cv (alphaDummy001 A))
                  (synCsn (Class.cv (alphaDummy003 A))))
                (Wff.classEq (Class.cv (alphaDummy002 A))
                  (synCsn (Class.cv (alphaDummy000 A))))
                (synWbr (Class.cv (alphaDummy003 A)) A (Class.cv (alphaDummy000 A))))))).fv

theorem support_mem_0003 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ((synWex z (synWex w
              (synW3a (Wff.classEq (Class.cv x) (synCsn (Class.cv z)))
                (Wff.classEq (Class.cv y) (synCsn (Class.cv w)))
                (synWbr (Class.cv z) A (Class.cv w)))))).fv) :=
  by
  with_reducible
    exact
      mem_pair_support_right x y
        ((synWex z (synWex w (synW3a (Wff.classEq (Class.cv x) (synCsn (Class.cv z)))
                (Wff.classEq (Class.cv y) (synCsn (Class.cv w)))
                (synWbr (Class.cv z) A (Class.cv w)))))).fv

theorem support_mem_0004 (A : Class) :
    (alphaDummy001 A) ∈
      (((Class.cv (alphaDummy001 A))).fv ∪ ((Class.cv (alphaDummy002 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0005 (A : Class) :
    (alphaDummy001 A) ∈
      (((synCcompl (Class.cab (alphaDummy006 A)
              (synWrex (alphaDummy007 A) (Class.cv (alphaDummy001 A))
                (Wff.classEq (Class.cv (alphaDummy006 A))
                  (synCphi (Class.cv (alphaDummy007 A)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy006 A)
              (synWrex (alphaDummy007 A) (Class.cv (alphaDummy002 A))
                (Wff.classEq (Class.cv (alphaDummy006 A))
                  (synCun (synCphi (Class.cv (alphaDummy007 A)))
                    (synCsn (synC0c)))))))).fv) :=
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

theorem support_mem_0008 (A : Class) :
    (alphaDummy001 A) ∈
      (((Class.cab (alphaDummy006 A)
            (synWrex (alphaDummy007 A) (Class.cv (alphaDummy001 A))
              (Wff.classEq (Class.cv (alphaDummy006 A))
                (synCphi (Class.cv (alphaDummy007 A))))))).fv ∪
        ((Class.cab (alphaDummy006 A)
            (synWrex (alphaDummy007 A) (Class.cv (alphaDummy001 A))
              (Wff.classEq (Class.cv (alphaDummy006 A))
                (synCphi (Class.cv (alphaDummy007 A))))))).fv) :=
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

theorem support_mem_0010 (A : Class) :
    (alphaDummy007 A) ∈ (((Class.cv (alphaDummy007 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0011 (x : Var) (y : Var) :
    (alphaDummy009 x y) ∈ (((Class.cv (alphaDummy009 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0012 (A : Class) :
    (alphaDummy014 A) ∈
      (((Wff.classMem (Class.cv (alphaDummy014 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy014 A)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy014 A))).fv) :=
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

theorem support_mem_0014 (A : Class) :
    (alphaDummy014 A) ∈ (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv) :=
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

theorem support_mem_0016 (A : Class) :
    (alphaDummy021 A) ∈
      (((synCnin (Class.cv (alphaDummy021 A)) (Class.cv (alphaDummy022 A)))).fv ∪
        ((synCnin (Class.cv (alphaDummy021 A)) (Class.cv (alphaDummy022 A)))).fv) :=
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

theorem support_mem_0018 (A : Class) :
    (alphaDummy021 A) ∈
      (((Class.cv (alphaDummy021 A))).fv ∪ ((Class.cv (alphaDummy022 A))).fv) :=
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

theorem support_mem_0020 (A : Class) :
    (alphaDummy022 A) ∈
      (((synCnin (Class.cv (alphaDummy021 A)) (Class.cv (alphaDummy022 A)))).fv ∪
        ((synCnin (Class.cv (alphaDummy021 A)) (Class.cv (alphaDummy022 A)))).fv) :=
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

theorem support_mem_0022 (A : Class) :
    (alphaDummy022 A) ∈
      (((Class.cv (alphaDummy021 A))).fv ∪ ((Class.cv (alphaDummy022 A))).fv) :=
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

theorem support_mem_0024 (A : Class) :
    (alphaDummy021 A) ∈
      (((synCcompl (Class.cv (alphaDummy021 A)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy022 A)))).fv) :=
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

theorem support_mem_0026 (A : Class) :
    (alphaDummy021 A) ∈
      (((Class.cv (alphaDummy021 A))).fv ∪ ((Class.cv (alphaDummy021 A))).fv) :=
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

theorem support_mem_0028 (A : Class) :
    (alphaDummy022 A) ∈
      (((synCcompl (Class.cv (alphaDummy021 A)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy022 A)))).fv) :=
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

theorem support_mem_0030 (A : Class) :
    (alphaDummy022 A) ∈
      (((Class.cv (alphaDummy022 A))).fv ∪ ((Class.cv (alphaDummy022 A))).fv) :=
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

theorem support_mem_0032 (A : Class) :
    (alphaDummy002 A) ∈
      (((Class.cv (alphaDummy001 A))).fv ∪ ((Class.cv (alphaDummy002 A))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0033 (A : Class) :
    (alphaDummy002 A) ∈
      (((synCcompl (Class.cab (alphaDummy006 A)
              (synWrex (alphaDummy007 A) (Class.cv (alphaDummy001 A))
                (Wff.classEq (Class.cv (alphaDummy006 A))
                  (synCphi (Class.cv (alphaDummy007 A)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy006 A)
              (synWrex (alphaDummy007 A) (Class.cv (alphaDummy002 A))
                (Wff.classEq (Class.cv (alphaDummy006 A))
                  (synCun (synCphi (Class.cv (alphaDummy007 A)))
                    (synCsn (synC0c)))))))).fv) :=
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

theorem support_mem_0036 (A : Class) :
    (alphaDummy002 A) ∈
      (((Class.cab (alphaDummy006 A)
            (synWrex (alphaDummy007 A) (Class.cv (alphaDummy002 A))
              (Wff.classEq (Class.cv (alphaDummy006 A))
                (synCun (synCphi (Class.cv (alphaDummy007 A))) (synCsn (synC0c))))))).fv ∪
        ((Class.cab (alphaDummy006 A)
            (synWrex (alphaDummy007 A) (Class.cv (alphaDummy002 A))
              (Wff.classEq (Class.cv (alphaDummy006 A))
                (synCun (synCphi (Class.cv (alphaDummy007 A)))
                  (synCsn (synC0c))))))).fv) :=
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

theorem support_mem_0038 (A : Class) :
    (alphaDummy007 A) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy007 A))))).fv ∪
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

theorem support_mem_0040 (A : Class) :
    (alphaDummy007 A) ∈
      (((synCphi (Class.cv (alphaDummy007 A)))).fv ∪
        ((synCphi (Class.cv (alphaDummy007 A)))).fv) :=
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

theorem support_mem_0042 (A : Class) :
    (alphaDummy003 A) ∈ (((Class.cv (alphaDummy003 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0043 (z : Var) : z ∈ (((Class.cv z)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0044 (A : Class) :
    (alphaDummy000 A) ∈ (((Class.cv (alphaDummy000 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0045 (w : Var) : w ∈ (((Class.cv w)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0046 (A : Class) :
    (alphaDummy003 A) ∈
      (((Class.cv (alphaDummy003 A))).fv ∪ ((Class.cv (alphaDummy000 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0047 (A : Class) :
    (alphaDummy003 A) ∈
      (((synCcompl (Class.cab (alphaDummy046 A)
              (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
                (Wff.classEq (Class.cv (alphaDummy046 A))
                  (synCphi (Class.cv (alphaDummy047 A)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy046 A)
              (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
                (Wff.classEq (Class.cv (alphaDummy046 A))
                  (synCun (synCphi (Class.cv (alphaDummy047 A)))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy048 z w)
              (synWrex (alphaDummy049 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy048 z w))
                  (synCphi (Class.cv (alphaDummy049 z w)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alphaDummy048 z w))
                  (synCun (synCphi (Class.cv (alphaDummy049 z w)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (alphaDummy003 A) ∈
      (((Class.cab (alphaDummy046 A)
            (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
              (Wff.classEq (Class.cv (alphaDummy046 A))
                (synCphi (Class.cv (alphaDummy047 A))))))).fv ∪
        ((Class.cab (alphaDummy046 A)
            (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
              (Wff.classEq (Class.cv (alphaDummy046 A))
                (synCphi (Class.cv (alphaDummy047 A))))))).fv) :=
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
      (((Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy048 z w))
                (synCphi (Class.cv (alphaDummy049 z w))))))).fv ∪
        ((Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy048 z w))
                (synCphi (Class.cv (alphaDummy049 z w))))))).fv) :=
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
    (alphaDummy047 A) ∈ (((Class.cv (alphaDummy047 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0053 (z : Var) (w : Var) :
    (alphaDummy049 z w) ∈ (((Class.cv (alphaDummy049 z w))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0054 (A : Class) :
    (alphaDummy054 A) ∈
      (((Wff.classMem (Class.cv (alphaDummy054 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy054 A)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy054 A))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0055 (z : Var) (w : Var) :
    (alphaDummy056 z w) ∈
      (((Wff.classMem (Class.cv (alphaDummy056 z w)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (alphaDummy056 z w)) (synC1c))).fv ∪
        ((Class.cv (alphaDummy056 z w))).fv) :=
  by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0056 (A : Class) :
    (alphaDummy054 A) ∈ (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0057 (z : Var) (w : Var) :
    (alphaDummy056 z w) ∈ (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0058 (A : Class) :
    (alphaDummy061 A) ∈
      (((synCnin (Class.cv (alphaDummy061 A)) (Class.cv (alphaDummy062 A)))).fv ∪
        ((synCnin (Class.cv (alphaDummy061 A)) (Class.cv (alphaDummy062 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0059 (z : Var) (w : Var) :
    (alphaDummy064 z w) ∈
      (((synCnin (Class.cv (alphaDummy064 z w)) (Class.cv (alphaDummy065 z w)))).fv ∪
        ((synCnin (Class.cv (alphaDummy064 z w)) (Class.cv (alphaDummy065 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0060 (A : Class) :
    (alphaDummy061 A) ∈
      (((Class.cv (alphaDummy061 A))).fv ∪ ((Class.cv (alphaDummy062 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0061 (z : Var) (w : Var) :
    (alphaDummy064 z w) ∈
      (((Class.cv (alphaDummy064 z w))).fv ∪ ((Class.cv (alphaDummy065 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0062 (A : Class) :
    (alphaDummy062 A) ∈
      (((synCnin (Class.cv (alphaDummy061 A)) (Class.cv (alphaDummy062 A)))).fv ∪
        ((synCnin (Class.cv (alphaDummy061 A)) (Class.cv (alphaDummy062 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0063 (z : Var) (w : Var) :
    (alphaDummy065 z w) ∈
      (((synCnin (Class.cv (alphaDummy064 z w)) (Class.cv (alphaDummy065 z w)))).fv ∪
        ((synCnin (Class.cv (alphaDummy064 z w)) (Class.cv (alphaDummy065 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0064 (A : Class) :
    (alphaDummy062 A) ∈
      (((Class.cv (alphaDummy061 A))).fv ∪ ((Class.cv (alphaDummy062 A))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0065 (z : Var) (w : Var) :
    (alphaDummy065 z w) ∈
      (((Class.cv (alphaDummy064 z w))).fv ∪ ((Class.cv (alphaDummy065 z w))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0066 (A : Class) :
    (alphaDummy061 A) ∈
      (((synCcompl (Class.cv (alphaDummy061 A)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy062 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0067 (z : Var) (w : Var) :
    (alphaDummy064 z w) ∈
      (((synCcompl (Class.cv (alphaDummy064 z w)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy065 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0068 (A : Class) :
    (alphaDummy061 A) ∈
      (((Class.cv (alphaDummy061 A))).fv ∪ ((Class.cv (alphaDummy061 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0069 (z : Var) (w : Var) :
    (alphaDummy064 z w) ∈
      (((Class.cv (alphaDummy064 z w))).fv ∪ ((Class.cv (alphaDummy064 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0070 (A : Class) :
    (alphaDummy062 A) ∈
      (((synCcompl (Class.cv (alphaDummy061 A)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy062 A)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0071 (z : Var) (w : Var) :
    (alphaDummy065 z w) ∈
      (((synCcompl (Class.cv (alphaDummy064 z w)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy065 z w)))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0072 (A : Class) :
    (alphaDummy062 A) ∈
      (((Class.cv (alphaDummy062 A))).fv ∪ ((Class.cv (alphaDummy062 A))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0073 (z : Var) (w : Var) :
    (alphaDummy065 z w) ∈
      (((Class.cv (alphaDummy065 z w))).fv ∪ ((Class.cv (alphaDummy065 z w))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0074 (A : Class) :
    (alphaDummy000 A) ∈
      (((Class.cv (alphaDummy003 A))).fv ∪ ((Class.cv (alphaDummy000 A))).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0075 (A : Class) :
    (alphaDummy000 A) ∈
      (((synCcompl (Class.cab (alphaDummy046 A)
              (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
                (Wff.classEq (Class.cv (alphaDummy046 A))
                  (synCphi (Class.cv (alphaDummy047 A)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy046 A)
              (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
                (Wff.classEq (Class.cv (alphaDummy046 A))
                  (synCun (synCphi (Class.cv (alphaDummy047 A)))
                    (synCsn (synC0c)))))))).fv) :=
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
      (((synCcompl (Class.cab (alphaDummy048 z w)
              (synWrex (alphaDummy049 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy048 z w))
                  (synCphi (Class.cv (alphaDummy049 z w)))))))).fv ∪ ((synCcompl
            (Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv w)
                (Wff.classEq (Class.cv (alphaDummy048 z w))
                  (synCun (synCphi (Class.cv (alphaDummy049 z w)))
                    (synCsn (synC0c)))))))).fv) :=
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
    (alphaDummy000 A) ∈
      (((Class.cab (alphaDummy046 A)
            (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
              (Wff.classEq (Class.cv (alphaDummy046 A))
                (synCun (synCphi (Class.cv (alphaDummy047 A))) (synCsn (synC0c))))))).fv ∪
        ((Class.cab (alphaDummy046 A)
            (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
              (Wff.classEq (Class.cv (alphaDummy046 A))
                (synCun (synCphi (Class.cv (alphaDummy047 A)))
                  (synCsn (synC0c))))))).fv) :=
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
      (((Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy048 z w))
                (synCun (synCphi (Class.cv (alphaDummy049 z w)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (alphaDummy048 z w)
            (synWrex (alphaDummy049 z w) (Class.cv w)
              (Wff.classEq (Class.cv (alphaDummy048 z w))
                (synCun (synCphi (Class.cv (alphaDummy049 z w)))
                  (synCsn (synC0c))))))).fv) :=
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
    (alphaDummy047 A) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy047 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0081 (z : Var) (w : Var) :
    (alphaDummy049 z w) ∈
      (((synCcompl (synCphi (Class.cv (alphaDummy049 z w))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0082 (A : Class) :
    (alphaDummy047 A) ∈
      (((synCphi (Class.cv (alphaDummy047 A)))).fv ∪
        ((synCphi (Class.cv (alphaDummy047 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem support_mem_0083 (z : Var) (w : Var) :
    (alphaDummy049 z w) ∈
      (((synCphi (Class.cv (alphaDummy049 z w)))).fv ∪
        ((synCphi (Class.cv (alphaDummy049 z w)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem focused_notmem_0000 (A : Class) : (alphaDummy000 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => hu)

theorem focused_notmem_0001 (A : Class) : (alphaDummy003 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 3 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 3
      (fun u hu => hu)

theorem parameter_support (x y z w : Var) (A : Class) (hz : z ∉ A.fv) (hw : w ∉ A.fv) :
    ∀ ⦃u : Var⦄,
      u ∈ A.fv →
        u ∈
          (synWex z (synWex w (synW3a (Wff.classEq (Class.cv x) (synCsn (Class.cv z)))
                  (Wff.classEq (Class.cv y) (synCsn (Class.cv w)))
                  (synWbr (Class.cv z) A (Class.cv w))))).fv :=
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

theorem focused_notmem_0002 (A : Class) : (alphaDummy004 A) ∉ A.fv :=
  by
  unfold alphaDummy004
  with_reducible
    exact
      (NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu =>
          Finset.mem_union_right _
            (parameter_support (alphaDummy001 A) (alphaDummy002 A) (alphaDummy003 A)
              (alphaDummy000 A) A (focused_notmem_0001 A) (focused_notmem_0000 A) hu)))

theorem wpp_notmem_0204 (A : Class) : (alphaDummy004 A) ∉ (A).fv := by
  exact (focused_notmem_0002 A)

theorem focused_notmem_0003 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_A_w : w ∉ A.fv) (dv_A_z : z ∉ A.fv) : (alphaDummy005 x y z w A) ∉ A.fv :=
  by
  unfold alphaDummy005
  with_reducible
    exact
      (NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu =>
          Finset.mem_union_right _ (parameter_support x y z w A dv_A_z dv_A_w hu)))

theorem wpp_notmem_0205 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_A_w : w ∉ A.fv) (dv_A_z : z ∉ A.fv) : (alphaDummy005 x y z w A) ∉ (A).fv := by
  exact (focused_notmem_0003 x y z w A dv_A_w dv_A_z)

theorem focused_notmem_0004 (A : Class) : (alphaDummy001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => hu)

theorem wpp_notmem_0206 (A : Class) : (alphaDummy001 A) ∉ (A).fv := by
  exact (focused_notmem_0004 A)

theorem wpp_notmem_0207 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem focused_notmem_0005 (A : Class) : (alphaDummy002 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => hu)

theorem wpp_notmem_0208 (A : Class) : (alphaDummy002 A) ∉ (A).fv := by
  exact (focused_notmem_0005 A)

theorem wpp_notmem_0209 (y : Var) (A : Class) (dv_A_y : y ∉ A.fv) : y ∉ (A).fv := by
  exact dv_A_y

theorem wpp_notmem_0210 (A : Class) : (alphaDummy003 A) ∉ (A).fv := by
  exact (focused_notmem_0001 A)

theorem wpp_notmem_0211 (z : Var) (A : Class) (dv_A_z : z ∉ A.fv) : z ∉ (A).fv := by
  exact dv_A_z

theorem wpp_notmem_0212 (A : Class) : (alphaDummy000 A) ∉ (A).fv := by
  exact (focused_notmem_0000 A)

theorem wpp_notmem_0213 (w : Var) (A : Class) (dv_A_w : w ∉ A.fv) : w ∉ (A).fv := by
  exact dv_A_w

end SingletonImageAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
